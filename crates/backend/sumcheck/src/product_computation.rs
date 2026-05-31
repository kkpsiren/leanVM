use fiat_shamir::*;
use field::*;
use poly::*;
use rayon::prelude::*;
use tracing::instrument;

use crate::{SumcheckComputation, sumcheck_prove_many_rounds};

#[derive(Debug)]
pub struct ProductComputation;

impl<EF: ExtensionField<PF<EF>>> SumcheckComputation<EF> for ProductComputation {
    type ExtraData = Vec<EF>;

    fn degree(&self) -> usize {
        2
    }
    #[inline(always)]
    fn eval_base(&self, _point: &[PF<EF>], _: &Self::ExtraData) -> EF {
        unreachable!()
    }
    #[inline(always)]
    fn eval_extension(&self, point: &[EF], _: &Self::ExtraData) -> EF {
        point[0] * point[1]
    }
    #[inline(always)]
    fn eval_packed_base(&self, point: &[PFPacking<EF>], _: &Self::ExtraData) -> EFPacking<EF> {
        EFPacking::<EF>::from(point[0] * point[1])
    }
    #[inline(always)]
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &Self::ExtraData) -> EFPacking<EF> {
        point[0] * point[1]
    }
}

#[instrument(skip_all)]
pub fn run_product_sumcheck<EF: ExtensionField<PF<EF>>>(
    pol_a: &MleRef<'_, EF>, // evals
    pol_b: &MleRef<'_, EF>, // weights
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);
    let first_sumcheck_poly = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| EFPacking::<EF>::to_ext_iter([e]).collect())
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| EFPacking::<EF>::to_ext_iter([e]).collect())
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| vec![e])
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| vec![e])
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = first_sumcheck_poly.evaluate(r1);

    if n_rounds == 1 {
        return (MultilinearPoint(vec![r1]), sum, pol_a.fold(r1), pol_b.fold(r1));
    }

    let (second_sumcheck_poly, folded) = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| {
                    EFPacking::<EF>::to_ext_iter([e]).collect()
                });
            (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| {
                    EFPacking::<EF>::to_ext_iter([e]).collect()
                });
            (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| vec![e]);
            (second_sumcheck_poly, MleGroupOwned::Extension(folded))
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| vec![e]);
            (second_sumcheck_poly, MleGroupOwned::Extension(folded))
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&second_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = second_sumcheck_poly.evaluate(r2);

    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        folded,
        Some(r2),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - 2,
        false,
        pow_bits,
    );

    challenges.splice(0..0, [r1, r2]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
}

pub fn compute_product_sumcheck_polynomial<
    F: PrimeCharacteristicRing + Copy + Send + Sync,
    EF: Field,
    EFPacking: Algebra<F> + Copy + Send + Sync,
>(
    pol_0: &[F],         // evals
    pol_1: &[EFPacking], // weights
    sum: EF,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> DensePolynomial<EF> {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());

    let num_elements = n;

    let (c0_packed, c2_packed) = if num_elements < PARALLEL_THRESHOLD {
        pol_0[..n / 2]
            .iter()
            .zip(pol_0[n / 2..].iter())
            .zip(pol_1[..n / 2].iter().zip(pol_1[n / 2..].iter()))
            .map(sumcheck_quadratic)
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        pol_0[..n / 2]
            .par_iter()
            .zip(pol_0[n / 2..].par_iter())
            .zip(pol_1[..n / 2].par_iter().zip(pol_1[n / 2..].par_iter()))
            .map(sumcheck_quadratic)
            .reduce(
                || (EFPacking::ZERO, EFPacking::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

pub fn fold_and_compute_product_sumcheck_polynomial<
    F: PrimeCharacteristicRing + Copy + Send + Sync + 'static,
    EF: Field,
    EFPacking: Algebra<F> + From<EF> + Copy + Send + Sync + 'static,
>(
    pol_0: &[F],         // evals
    pol_1: &[EFPacking], // weights
    prev_folding_factor: EF,
    sum: EF,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> (DensePolynomial<EF>, Vec<Vec<EFPacking>>) {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let prev_folding_factor_packed = EFPacking::from(prev_folding_factor);

    let mut pol_0_folded = unsafe { uninitialized_vec::<EFPacking>(n / 2) };
    let mut pol_1_folded = unsafe { uninitialized_vec::<EFPacking>(n / 2) };

    #[allow(clippy::type_complexity)]
    let process_element = |(p0_prev, p0_f): (((&F, &F), (&F, &F)), (&mut EFPacking, &mut EFPacking)),
                           (p1_prev, p1_f): (
        ((&EFPacking, &EFPacking), (&EFPacking, &EFPacking)),
        (&mut EFPacking, &mut EFPacking),
    )| {
        let diff_0 = *p0_prev.1.0 - *p0_prev.0.0;
        let diff_1 = *p0_prev.1.1 - *p0_prev.0.1;
        let x_0 = prev_folding_factor_packed * diff_0 + *p0_prev.0.0;
        let x_1 = prev_folding_factor_packed * diff_1 + *p0_prev.0.1;
        *p0_f.0 = x_0;
        *p0_f.1 = x_1;

        let y_0 = prev_folding_factor_packed * (*p1_prev.1.0 - *p1_prev.0.0) + *p1_prev.0.0;
        let y_1 = prev_folding_factor_packed * (*p1_prev.1.1 - *p1_prev.0.1) + *p1_prev.0.1;
        *p1_f.0 = y_0;
        *p1_f.1 = y_1;

        sumcheck_quadratic(((&x_0, &x_1), (&y_0, &y_1)))
    };

    let (c0_packed, c2_packed) = if n < PARALLEL_THRESHOLD {
        zip_fold_2(pol_0, &mut pol_0_folded)
            .zip(zip_fold_2(pol_1, &mut pol_1_folded))
            .map(|(p0, p1)| process_element(p0, p1))
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        par_zip_fold_2(pol_0, &mut pol_0_folded)
            .zip(par_zip_fold_2(pol_1, &mut pol_1_folded))
            .map(|(p0, p1)| process_element(p0, p1))
            .reduce(
                || (EFPacking::ZERO, EFPacking::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    (DensePolynomial::new(vec![c0, c1, c2]), vec![pol_0_folded, pol_1_folded])
}

#[inline(always)]
pub fn sumcheck_quadratic<F, EF>(((&x_0, &x_1), (&y_0, &y_1)): ((&F, &F), (&EF, &EF))) -> (EF, EF)
where
    F: PrimeCharacteristicRing + Copy,
    EF: Algebra<F> + Copy,
{
    let constant = y_0 * x_0;
    let quadratic = (y_1 - y_0) * (x_1 - x_0);
    (constant, quadratic)
}

// --- Stacked (segmented) variants: same product sumcheck, but `evals` is read from a
// `StackedPoly` (a logical concatenation of base-field segments) instead of one contiguous
// slice, so the full stacked polynomial is never materialized. `weights` stays contiguous.
// The high-bit fold pairs index `i` with `i + n/2`, crossing segment boundaries, so we read
// the relevant halves/quarters per "run" (a range where every queried source stays inside one
// segment) — each run is a tight packed-SIMD loop. After the first fold the data is contiguous
// and owned, so subsequent rounds reuse the standard machinery.

/// Round-1 sumcheck polynomial over the stacked `evals` (no fold yet).
pub fn compute_product_sumcheck_polynomial_stacked<EF: ExtensionField<PF<EF>>>(
    stacked: &StackedPoly<'_, EF>,
    weights: &[EFPacking<EF>], // contiguous, len = n_packed
    sum: EF,
) -> DensePolynomial<EF> {
    let n_packed = weights.len();
    let half = n_packed / 2;
    let runs = stacked.runs([0, half], half);

    let mut c0_packed = EFPacking::<EF>::ZERO;
    let mut c2_packed = EFPacking::<EF>::ZERO;
    for run in &runs {
        let (s, lo, hi) = (run.start, run.srcs[0], run.srcs[1]);
        let (rc0, rc2) = (0..run.len)
            .into_par_iter()
            .map(|k| {
                let x0 = lo.map_or(PFPacking::<EF>::ZERO, |sl| sl[k]);
                let x1 = hi.map_or(PFPacking::<EF>::ZERO, |sl| sl[k]);
                sumcheck_quadratic(((&x0, &x1), (&weights[s + k], &weights[half + s + k])))
            })
            .reduce(
                || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            );
        c0_packed += rc0;
        c2_packed += rc2;
    }

    let c0 = EFPacking::<EF>::to_ext_iter([c0_packed]).sum::<EF>();
    let c2 = EFPacking::<EF>::to_ext_iter([c2_packed]).sum::<EF>();
    let c1 = sum - c0.double() - c2;
    DensePolynomial::new(vec![c0, c1, c2])
}

/// Fold the stacked `evals` (and `weights`) by `prev_folding_factor` along the highest
/// variable, returning the (contiguous, owned) folded `[evals, weights]` and the round-2
/// sumcheck polynomial.
pub fn fold_and_compute_product_sumcheck_polynomial_stacked<EF: ExtensionField<PF<EF>>>(
    stacked: &StackedPoly<'_, EF>,
    weights: &[EFPacking<EF>],
    prev_folding_factor: EF,
    sum: EF,
) -> (DensePolynomial<EF>, Vec<Vec<EFPacking<EF>>>) {
    let n_packed = weights.len();
    let q = n_packed / 4;
    let prev_packed = EFPacking::<EF>::from(prev_folding_factor);
    let runs = stacked.runs([0, q, 2 * q, 3 * q], q);

    let mut out0 = unsafe { uninitialized_vec::<EFPacking<EF>>(n_packed / 2) };
    let mut out1 = unsafe { uninitialized_vec::<EFPacking<EF>>(n_packed / 2) };
    let (out0_lo, out0_hi) = out0.split_at_mut(q);
    let (out1_lo, out1_hi) = out1.split_at_mut(q);

    let mut c0_packed = EFPacking::<EF>::ZERO;
    let mut c2_packed = EFPacking::<EF>::ZERO;
    for run in &runs {
        let (s, len, srcs) = (run.start, run.len, run.srcs);
        let (rc0, rc2) = out0_lo[s..s + len]
            .par_iter_mut()
            .zip(out0_hi[s..s + len].par_iter_mut())
            .zip(out1_lo[s..s + len].par_iter_mut())
            .zip(out1_hi[s..s + len].par_iter_mut())
            .enumerate()
            .map(|(k, (((o0l, o0h), o1l), o1h))| {
                let xll = srcs[0].map_or(PFPacking::<EF>::ZERO, |sl| sl[k]);
                let xlr = srcs[1].map_or(PFPacking::<EF>::ZERO, |sl| sl[k]);
                let xrl = srcs[2].map_or(PFPacking::<EF>::ZERO, |sl| sl[k]);
                let xrr = srcs[3].map_or(PFPacking::<EF>::ZERO, |sl| sl[k]);
                let x0 = prev_packed * (xrl - xll) + xll;
                let x1 = prev_packed * (xrr - xlr) + xlr;
                *o0l = x0;
                *o0h = x1;

                let (wll, wlr, wrl, wrr) = (
                    weights[s + k],
                    weights[q + s + k],
                    weights[2 * q + s + k],
                    weights[3 * q + s + k],
                );
                let y0 = prev_packed * (wrl - wll) + wll;
                let y1 = prev_packed * (wrr - wlr) + wlr;
                *o1l = y0;
                *o1h = y1;

                sumcheck_quadratic(((&x0, &x1), (&y0, &y1)))
            })
            .reduce(
                || (EFPacking::<EF>::ZERO, EFPacking::<EF>::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            );
        c0_packed += rc0;
        c2_packed += rc2;
    }

    let c0 = EFPacking::<EF>::to_ext_iter([c0_packed]).sum::<EF>();
    let c2 = EFPacking::<EF>::to_ext_iter([c2_packed]).sum::<EF>();
    let c1 = sum - c0.double() - c2;
    (DensePolynomial::new(vec![c0, c1, c2]), vec![out0, out1])
}

/// Stacked analogue of [`run_product_sumcheck`]: only the first fold reads from the segmented
/// `evals`; everything afterwards is contiguous and owned.
pub fn run_product_sumcheck_stacked<EF: ExtensionField<PF<EF>>>(
    stacked: &StackedPoly<'_, EF>,
    weights: &[EFPacking<EF>],
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);

    let first_sumcheck_poly = compute_product_sumcheck_polynomial_stacked(stacked, weights, sum);
    prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = first_sumcheck_poly.evaluate(r1);

    if n_rounds == 1 {
        let folded_evals = MleOwned::Extension(stacked.fold_to_owned(r1));
        let folded_weights = MleRef::ExtensionPacked(weights).fold(r1);
        return (MultilinearPoint(vec![r1]), sum, folded_evals, folded_weights);
    }

    let (second_sumcheck_poly, folded) =
        fold_and_compute_product_sumcheck_polynomial_stacked(stacked, weights, r1, sum);
    prover_state.add_sumcheck_polynomial(&second_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = second_sumcheck_poly.evaluate(r2);

    let folded = MleGroupOwned::ExtensionPacked(folded);
    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        folded,
        Some(r2),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - 2,
        false,
        pow_bits,
    );

    challenges.splice(0..0, [r1, r2]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
}
