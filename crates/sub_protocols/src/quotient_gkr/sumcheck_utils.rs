use std::ops::{Add, AddAssign, Mul, Sub};

use backend::*;

use crate::quotient_gkr::layers::unpack_and_unreverse_active;

pub(super) fn even_odd_split<T: Copy>(v: &[T]) -> (ArenaVec<T>, ArenaVec<T>) {
    (
        v.iter().step_by(2).copied().collect(),
        v.iter().skip(1).step_by(2).copied().collect(),
    )
}

// ---------------------------------------------------------------------------
// logup* product optimization
// ---------------------------------------------------------------------------
//
// Standard GKR for Σ nᵢ/dᵢ combines two fractions a/b + c/d into
//   num = a·d + b·c,   den = b·d
// and the per-layer sumcheck has to handle the 4-term expression
//   num_l·den_r + num_r·den_l + α·den_l·den_r.
//
// The optimization (logup*) additionally sets aside the term `a·c` while
// building the layer (`prods`). When the three claims (den, num, prod = a·c)
// arrive at a point, they are folded with powers of a single challenge `g`:
//   den + g·num + g²·prod = b·d + g·(a·d + b·c) + g²·a·c = (b + g·a)·(d + g·c).
//
// So if we form `comb = den + g·num` once per layer, the sumcheck becomes a
// plain product `comb_l · comb_r`. We keep the numerator `num` around (folded
// through the same challenges) to recover `den = comb − g·num`, and we keep the
// stored `prods` polynomial (also folded through the same challenges) so that
// the *next* layer's product claim pops out for free — no separate pass.

#[derive(Clone, Copy, Default)]
struct RoundCoeffs<T: Copy> {
    c0: T,
    c2: T,
}

impl<T: Copy + Default> RoundCoeffs<T> {
    fn zero() -> Self {
        Self::default()
    }
}

impl<T: Copy + AddAssign> AddAssign for RoundCoeffs<T> {
    fn add_assign(&mut self, rhs: Self) {
        self.c0 += rhs.c0;
        self.c2 += rhs.c2;
    }
}

impl<T: Copy + AddAssign> Add for RoundCoeffs<T> {
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self {
        self += rhs;
        self
    }
}

impl<T, W> Mul<W> for RoundCoeffs<T>
where
    T: Copy + Mul<W, Output = T>,
    W: Copy,
{
    type Output = Self;
    fn mul(self, w: W) -> Self {
        Self {
            c0: self.c0 * w,
            c2: self.c2 * w,
        }
    }
}

/// Round coefficients for the product `comb_l · comb_r`, where each argument is
/// the `(value@0, value@1)` pair of the current sumcheck variable.
#[inline(always)]
fn prod_coeffs<T>(cl: (T, T), cr: (T, T)) -> RoundCoeffs<T>
where
    T: Copy + Mul<Output = T> + Sub<Output = T>,
{
    RoundCoeffs {
        c0: cl.0 * cr.0,
        c2: (cl.1 - cl.0) * (cr.1 - cr.0),
    }
}

#[inline(always)]
fn within_pt<EF: Copy>(remaining_eq: &[EF], head_len: usize) -> Vec<EF> {
    remaining_eq[head_len..remaining_eq.len() - 1]
        .iter()
        .rev()
        .copied()
        .collect()
}

fn finalize_round<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    coeffs: RoundCoeffs<EFPacking<EF>>,
    eq_alpha: EF,
    sum: &mut EF,
    mmf: &mut EF,
    padding_correction: EF,
) -> EF {
    let c0_raw: EF = EFPacking::<EF>::to_ext_iter([coeffs.c0]).sum::<EF>() + padding_correction;
    let c2_raw: EF = EFPacking::<EF>::to_ext_iter([coeffs.c2]).sum();
    let bare = build_bare_from_coeffs(c0_raw, c2_raw, eq_alpha, *sum, *mmf);
    prover_state.add_sumcheck_polynomial(&bare.coeffs, Some(eq_alpha));
    let r = prover_state.sample();
    let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r) + eq_alpha * r;
    *sum = eq_eval * bare.evaluate(r);
    *mmf *= eq_eval;
    r
}

/// Forms `comb = den + g·num` (base-field numerators).
pub(super) fn form_comb_base<EF: ExtensionField<PF<EF>>>(
    nums: &[PFPacking<EF>],
    dens: &[EFPacking<EF>],
    g: EF,
) -> ArenaVec<EFPacking<EF>> {
    debug_assert_eq!(nums.len(), dens.len());
    let g_packed = EFPacking::<EF>::from(g);
    ArenaVec::par_collect(nums.len(), |i| dens[i] + g_packed * nums[i])
}

/// Forms `comb = den + g·num` (extension-field numerators).
pub(super) fn form_comb_ext<EF: ExtensionField<PF<EF>>>(
    nums: &[EFPacking<EF>],
    dens: &[EFPacking<EF>],
    g: EF,
) -> ArenaVec<EFPacking<EF>> {
    debug_assert_eq!(nums.len(), dens.len());
    let g_packed = EFPacking::<EF>::from(g);
    ArenaVec::par_collect(nums.len(), |i| dens[i] + g_packed * nums[i])
}

/// Final evaluations of a layer's sumcheck at the sampled point: numerator and
/// `comb` halves, plus the (folded) `prods` halves used to recover the next
/// layer's product claim. `ac_*` are `None` for the finest (input) layer, which
/// does not carry a `prods` polynomial (it is processed last and never has to
/// produce a downstream product claim).
pub(super) struct LayerEvals<EF> {
    pub num_l: EF,
    pub num_r: EF,
    pub comb_l: EF,
    pub comb_r: EF,
    pub ac_l: Option<EF>,
    pub ac_r: Option<EF>,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn quotient_sumcheck_prove_packed_br_base<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    packed_nums: &[PFPacking<EF>],
    packed_comb: &[EFPacking<EF>],
    packed_prods: Option<&[EFPacking<EF>]>,
    parent_chunk_log: usize,
    eq_point: &[EF],
    expected_sum: EF,
) -> (Vec<EF>, LayerEvals<EF>) {
    let w = packing_log_width::<EF>();
    debug_assert!(parent_chunk_log >= w + 3);
    debug_assert_eq!(packed_nums.len(), packed_comb.len());
    let active_chunks = (packed_nums.len() << w) >> parent_chunk_log;

    let k = eq_point.len();
    let mut remaining_eq = eq_point.to_vec();
    let head_len = (k + 1).saturating_sub(parent_chunk_log);
    let mut q_natural = vec![];
    let mut mmf = EF::ONE;
    let mut sum = expected_sum;

    let outer_point = remaining_eq[..head_len].to_vec();
    let eq_outer: ArenaVec<EF> = eval_eq(&outer_point);

    let padding_correction = mle_of_zeros_then_ones(active_chunks, &outer_point);

    let eq_alpha_0 = *remaining_eq.last().unwrap();
    let eq_within_0: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let coeffs_0 = compute_round_packed::<EF>(packed_comb, parent_chunk_log, &eq_outer, &eq_within_0);
    let r0 = finalize_round(
        prover_state,
        coeffs_0,
        eq_alpha_0,
        &mut sum,
        &mut mmf,
        padding_correction,
    );
    q_natural.push(r0);
    remaining_eq.pop();

    let eq_alpha_1 = *remaining_eq.last().unwrap();
    let eq_within_1: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));
    let (nums_ext, comb_ext, prods_ext, coeffs_1) = fold_and_compute_round_packed::<EF, _>(
        packed_nums,
        packed_comb,
        packed_prods,
        parent_chunk_log,
        r0,
        &eq_outer,
        &eq_within_1,
    );
    let r1 = finalize_round(
        prover_state,
        coeffs_1,
        eq_alpha_1,
        &mut sum,
        &mut mmf,
        padding_correction,
    );
    q_natural.push(r1);
    remaining_eq.pop();

    run_phase1_sumcheck(
        prover_state,
        ArenaCow::Owned(nums_ext),
        ArenaCow::Owned(comb_ext),
        prods_ext.map(ArenaCow::Owned),
        parent_chunk_log - 2,
        remaining_eq,
        q_natural,
        sum,
        mmf,
        Some(eq_outer),
        Some(r1),
    )
}

/// bit-reversed by chunk + Packed
#[allow(clippy::too_many_arguments)]
pub(super) fn run_phase1_sumcheck<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    mut nums: ArenaCow<'a, EFPacking<EF>>,
    mut comb: ArenaCow<'a, EFPacking<EF>>,
    mut prods: Option<ArenaCow<'a, EFPacking<EF>>>,
    mut layer_chunk_log: usize,
    mut remaining_eq: Vec<EF>,
    mut q_natural: Vec<EF>,
    mut sum: EF,
    mut mmf: EF,
    precomputed_eq_outer: Option<ArenaVec<EF>>,
    initial_pending_r: Option<EF>,
) -> (Vec<EF>, LayerEvals<EF>) {
    let w = packing_log_width::<EF>();

    if layer_chunk_log <= w {
        assert!(initial_pending_r.is_none());
        let (num_l, num_r) = even_odd_split(&unpack_and_unreverse_active::<EF>(nums.as_ref(), layer_chunk_log));
        let (comb_l, comb_r) = even_odd_split(&unpack_and_unreverse_active::<EF>(comb.as_ref(), layer_chunk_log));
        let ac = prods
            .as_ref()
            .map(|p| even_odd_split(&unpack_and_unreverse_active::<EF>(p.as_ref(), layer_chunk_log)));
        return run_phase2_sumcheck(
            prover_state,
            num_l,
            num_r,
            comb_l,
            comb_r,
            ac,
            remaining_eq,
            q_natural,
            sum,
            mmf,
        );
    }

    let head_len = (remaining_eq.len() + 1).saturating_sub(layer_chunk_log);
    let outer_point: Vec<EF> = remaining_eq[..head_len].to_vec();
    let eq_outer: ArenaVec<EF> = precomputed_eq_outer.unwrap_or_else(|| eval_eq(&outer_point));

    let active_chunks = (nums.len() << w) >> (layer_chunk_log + usize::from(initial_pending_r.is_some()));

    let padding_correction = mle_of_zeros_then_ones(active_chunks, &outer_point);

    let mut pending_r: Option<EF> = initial_pending_r;
    while layer_chunk_log > w + 1 && remaining_eq.len() > w + 1 {
        let eq_alpha = *remaining_eq.last().unwrap();
        let eq_within: ArenaVec<_> = eval_eq_packed(&within_pt(&remaining_eq, head_len));

        let coeffs = if let Some(prev_r) = pending_r.take() {
            let (new_nums, new_comb, new_prods, c) = fold_and_compute_round_packed::<EF, _>(
                nums.as_ref(),
                comb.as_ref(),
                prods.as_ref().map(|p| p.as_ref()),
                layer_chunk_log + 1,
                prev_r,
                &eq_outer,
                &eq_within,
            );
            nums = ArenaCow::Owned(new_nums);
            comb = ArenaCow::Owned(new_comb);
            prods = new_prods.map(ArenaCow::Owned);
            c
        } else {
            compute_round_packed::<EF>(comb.as_ref(), layer_chunk_log, &eq_outer, &eq_within)
        };

        let r = finalize_round(prover_state, coeffs, eq_alpha, &mut sum, &mut mmf, padding_correction);
        pending_r = Some(r);
        layer_chunk_log -= 1;
        q_natural.push(r);
        remaining_eq.pop();
    }

    if let Some(prev_r) = pending_r {
        let prev_bit = layer_chunk_log - 1 - w;
        let mul = |x: EFPacking<EF>, a: EF| x * a;
        nums = ArenaCow::Owned(fold_multilinear_at_bit(nums.as_ref(), prev_r, prev_bit, &mul, false));
        comb = ArenaCow::Owned(fold_multilinear_at_bit(comb.as_ref(), prev_r, prev_bit, &mul, false));
        prods = prods.map(|p| ArenaCow::Owned(fold_multilinear_at_bit(p.as_ref(), prev_r, prev_bit, &mul, false)));
    }

    let nums_nat = unpack_and_unreverse_active::<EF>(nums.as_ref(), layer_chunk_log);
    let comb_nat = unpack_and_unreverse_active::<EF>(comb.as_ref(), layer_chunk_log);
    let (num_l, num_r) = even_odd_split(&nums_nat);
    let (comb_l, comb_r) = even_odd_split(&comb_nat);
    let ac = prods
        .as_ref()
        .map(|p| even_odd_split(&unpack_and_unreverse_active::<EF>(p.as_ref(), layer_chunk_log)));
    run_phase2_sumcheck(
        prover_state,
        num_l,
        num_r,
        comb_l,
        comb_r,
        ac,
        remaining_eq,
        q_natural,
        sum,
        mmf,
    )
}

// Normal ordering (not bit-reversed) + not packed
#[allow(clippy::too_many_arguments)]
pub(super) fn run_phase2_sumcheck<EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    mut num_l: ArenaVec<EF>,
    mut num_r: ArenaVec<EF>,
    mut comb_l: ArenaVec<EF>,
    mut comb_r: ArenaVec<EF>,
    ac: Option<(ArenaVec<EF>, ArenaVec<EF>)>,
    mut remaining_eq: Vec<EF>,
    mut q_natural: Vec<EF>,
    mut sum: EF,
    mut mmf: EF,
) -> (Vec<EF>, LayerEvals<EF>) {
    let (mut ac_l, mut ac_r) = match ac {
        Some((l, r)) => (Some(l), Some(r)),
        None => (None, None),
    };
    let eq_prefix_init = &remaining_eq[..remaining_eq.len().saturating_sub(1)];
    let mut eq_table: ArenaVec<EF> = eval_eq(eq_prefix_init);

    for _round in 0..remaining_eq.len() {
        let eq_alpha = *remaining_eq.last().unwrap();

        let active_l = comb_l.len();
        let active_r = comb_r.len();
        let active_pairs = active_l.div_ceil(2);
        let fully_active = active_r / 2;

        let term = |j: usize| -> RoundCoeffs<EF> {
            let coeffs = if j < fully_active {
                prod_coeffs::<EF>((comb_l[2 * j], comb_l[2 * j + 1]), (comb_r[2 * j], comb_r[2 * j + 1]))
            } else {
                let get_pair = |arr: &[EF], idx: usize, pad: EF| {
                    (
                        arr.get(idx).copied().unwrap_or(pad),
                        arr.get(idx + 1).copied().unwrap_or(pad),
                    )
                };
                prod_coeffs::<EF>(get_pair(&comb_l, 2 * j, EF::ONE), get_pair(&comb_r, 2 * j, EF::ONE))
            };
            coeffs * eq_table[j]
        };

        let acc: RoundCoeffs<EF> = if active_pairs > PARALLEL_THRESHOLD {
            parallel::map_reduce(active_pairs, RoundCoeffs::zero, term, Add::add)
        } else {
            (0..active_pairs).map(term).fold(RoundCoeffs::<EF>::zero(), Add::add)
        };

        let eq_prefix = &remaining_eq[..remaining_eq.len() - 1];
        let padding_correction = mle_of_zeros_then_ones(active_pairs, eq_prefix);

        let bare = build_bare_from_coeffs(acc.c0 + padding_correction, acc.c2, eq_alpha, sum, mmf);

        prover_state.add_sumcheck_polynomial(&bare.coeffs, Some(eq_alpha));
        let r = prover_state.sample();
        let eq_eval = (EF::ONE - eq_alpha) * (EF::ONE - r) + eq_alpha * r;
        sum = eq_eval * bare.evaluate(r);
        mmf *= eq_eval;

        num_l = fold_normal_with_padding(&num_l, r, EF::ZERO);
        num_r = fold_normal_with_padding(&num_r, r, EF::ZERO);
        comb_l = fold_normal_with_padding(&comb_l, r, EF::ONE);
        comb_r = fold_normal_with_padding(&comb_r, r, EF::ONE);
        // `prods = num_l·num_r`, so padding (num = 0) folds with a 0 pad value.
        ac_l = ac_l.map(|a| fold_normal_with_padding(&a, r, EF::ZERO));
        ac_r = ac_r.map(|a| fold_normal_with_padding(&a, r, EF::ZERO));

        let new_eq_len = eq_table.len() / 2;
        if new_eq_len > 0 {
            let fold_eq = |i: usize| eq_table[2 * i] + eq_table[2 * i + 1];
            eq_table = if new_eq_len >= PARALLEL_THRESHOLD {
                ArenaVec::par_collect(new_eq_len, fold_eq)
            } else {
                (0..new_eq_len).map(fold_eq).collect()
            };
        }

        q_natural.push(r);
        remaining_eq.pop();
    }

    q_natural.reverse();
    let evals = LayerEvals {
        num_l: num_l[0],
        num_r: num_r[0],
        comb_l: comb_l[0],
        comb_r: comb_r[0],
        ac_l: ac_l.map(|a| a[0]),
        ac_r: ac_r.map(|a| a[0]),
    };
    (q_natural, evals)
}

fn fold_normal_with_padding<EF: ExtensionField<PF<EF>>>(m: &[EF], r: EF, pad_value: EF) -> ArenaVec<EF> {
    let active = m.len();
    let new_active = active.div_ceil(2);
    assert!(new_active != 0);
    let mut out: ArenaVec<EF> = unsafe { ArenaVec::uninitialized(new_active) };

    let compute = |i: usize, slot: &mut EF| {
        let a = m[2 * i];
        let b = if 2 * i + 1 < active { m[2 * i + 1] } else { pad_value };
        *slot = a + (b - a) * r;
    };

    if new_active < PARALLEL_THRESHOLD {
        out.iter_mut().enumerate().for_each(|(i, slot)| compute(i, slot));
    } else {
        parallel::par_for_each_mut(&mut out, compute);
    }
    out
}

/// Round coefficients for `comb_l · comb_r` from a packed, chunk-bit-reversed
/// `comb` polynomial (no fold).
fn compute_round_packed<EF: ExtensionField<PF<EF>>>(
    comb: &[EFPacking<EF>],
    layer_chunk_log: usize,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> RoundCoeffs<EFPacking<EF>> {
    let w = packing_log_width::<EF>();
    debug_assert!(layer_chunk_log >= w + 2);
    let layer_packed = 1usize << (layer_chunk_log - w);
    let half = layer_packed / 2;
    let quarter = layer_packed / 4;
    debug_assert!(comb.len().is_multiple_of(layer_packed));
    debug_assert_eq!(eq_within.len(), quarter);

    let n_chunks = comb.len() / layer_packed;
    parallel::map_reduce(
        n_chunks,
        RoundCoeffs::zero,
        |c| {
            let d_c = &comb[c * layer_packed..][..layer_packed];
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let mut local = RoundCoeffs::<EFPacking<EF>>::zero();
            for inner in 0..quarter {
                let coeffs = prod_coeffs::<EFPacking<EF>>(
                    (d_c[inner], d_c[inner + quarter]),
                    (d_c[inner + half], d_c[inner + half + quarter]),
                );
                local += coeffs * eq_within[inner];
            }
            local * eq_o
        },
        Add::add,
    )
}

/// Folds `nums`, `comb`, and (optionally) `prods` by `prev_r`, and computes this
/// round's `comb_l·comb_r` coefficients. `nums` is kept (and folded) only to
/// recover its evaluations; `prods` is kept to recover the next layer's product
/// claim. Neither contributes to the round coefficients.
#[allow(clippy::type_complexity)]
fn fold_and_compute_round_packed<EF: ExtensionField<PF<EF>>, N>(
    nums: &[N],
    comb: &[EFPacking<EF>],
    prods: Option<&[EFPacking<EF>]>,
    layer_chunk_log_old: usize,
    prev_r: EF,
    eq_outer: &[EF],
    eq_within: &[EFPacking<EF>],
) -> (
    ArenaVec<EFPacking<EF>>,
    ArenaVec<EFPacking<EF>>,
    Option<ArenaVec<EFPacking<EF>>>,
    RoundCoeffs<EFPacking<EF>>,
)
where
    N: PrimeCharacteristicRing + Copy + Send + Sync,
    EFPacking<EF>: Algebra<N>,
{
    let w = packing_log_width::<EF>();
    debug_assert!(layer_chunk_log_old >= w + 3);
    let in_packed = 1usize << (layer_chunk_log_old - w);
    let in_half = in_packed / 2;
    let in_quarter = in_packed / 4;
    let in_eighth = in_packed / 8;
    let out_packed = in_packed / 2;
    let out_half = out_packed / 2;
    let out_quarter = out_packed / 4;
    debug_assert!(nums.len().is_multiple_of(in_packed));
    debug_assert_eq!(comb.len(), nums.len());
    debug_assert_eq!(eq_within.len(), in_eighth);

    let active_out_packed = nums.len() / 2;
    let mut new_nums: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(active_out_packed) };
    let mut new_comb: ArenaVec<EFPacking<EF>> = unsafe { ArenaVec::uninitialized(active_out_packed) };
    let mut new_prods: Option<ArenaVec<EFPacking<EF>>> =
        prods.map(|_| unsafe { ArenaVec::uninitialized(active_out_packed) });
    let prev_r_packed: EFPacking<EF> = <EFPacking<EF> as From<EF>>::from(prev_r);

    let n_chunks = nums.len() / in_packed;
    let nn = parallel::SendPtr(new_nums.as_mut_ptr());
    let nd = parallel::SendPtr(new_comb.as_mut_ptr());
    let na = new_prods.as_mut().map(|p| parallel::SendPtr(p.as_mut_ptr()));
    let coeffs = parallel::map_reduce(
        n_chunks,
        RoundCoeffs::zero,
        |c| {
            let n_c = &nums[c * in_packed..][..in_packed];
            let d_c = &comb[c * in_packed..][..in_packed];
            let p_c = prods.map(|p| &p[c * in_packed..][..in_packed]);
            let nn_c = unsafe { nn.slice(c * out_packed, out_packed) };
            let nd_c = unsafe { nd.slice(c * out_packed, out_packed) };
            let mut na_c = na.as_ref().map(|na| unsafe { na.slice(c * out_packed, out_packed) });
            let eq_o: EF = eq_outer.get(c).copied().unwrap_or(EF::ONE);
            let mut local = RoundCoeffs::<EFPacking<EF>>::zero();
            for i in 0..in_eighth {
                for side in 0..2 {
                    for c in 0..2 {
                        let lo = i + side * in_half + c * in_eighth;
                        let hi = lo + in_quarter;
                        let out = i + side * out_half + c * out_quarter;
                        nn_c[out] = prev_r_packed * (n_c[hi] - n_c[lo]) + n_c[lo];
                        nd_c[out] = d_c[lo] + (d_c[hi] - d_c[lo]) * prev_r;
                        if let (Some(p_c), Some(na_c)) = (p_c, na_c.as_deref_mut()) {
                            na_c[out] = p_c[lo] + (p_c[hi] - p_c[lo]) * prev_r;
                        }
                    }
                }
                let round = prod_coeffs::<EFPacking<EF>>(
                    (nd_c[i], nd_c[i + out_quarter]),
                    (nd_c[i + out_half], nd_c[i + out_half + out_quarter]),
                );
                local += round * eq_within[i];
            }
            local * eq_o
        },
        Add::add,
    );

    (new_nums, new_comb, new_prods, coeffs)
}

fn build_bare_from_coeffs<EF: ExtensionField<PF<EF>>>(
    c0_raw: EF,
    c2_raw: EF,
    eq_alpha: EF,
    sum: EF,
    mmf: EF,
) -> DensePolynomial<EF> {
    let c0_mmf = c0_raw * mmf;
    let c2_mmf = c2_raw * mmf;
    let h1_mmf = (sum - (EF::ONE - eq_alpha) * c0_mmf) / eq_alpha;
    let c1_mmf = h1_mmf - c0_mmf - c2_mmf;
    DensePolynomial::new(vec![c0_mmf, c1_mmf, c2_mmf])
}
