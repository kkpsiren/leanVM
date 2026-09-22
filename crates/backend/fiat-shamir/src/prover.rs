use crate::challenger::Challenger;
use crate::{MerklePaths, PrunedMerklePaths, *};
use field::Field;
use field::PackedValue;
use field::PrimeCharacteristicRing;
use field::PrimeField64;
use field::integers::QuotientMap;
use koala_bear::KoalaBearExtension;
use koala_bear::symmetric::Permutation;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;
use std::{fmt::Debug, time::Instant};
use symetric::CAPACITY;
use symetric::RATE;
use symetric::WIDTH;

static POW_GRINDING_NANOS: AtomicU64 = AtomicU64::new(0);

pub fn pow_grinding_time() -> Duration {
    Duration::from_nanos(POW_GRINDING_NANOS.load(Ordering::Relaxed))
}

pub fn reset_pow_grinding_time() {
    POW_GRINDING_NANOS.store(0, Ordering::Relaxed);
}

#[derive(Debug)]
pub struct ProverState<EF: KoalaBearExtension, P> {
    challenger: Challenger<PF<EF>, P>,
    transcript: Vec<PF<EF>>,
    merkle_paths: Vec<PrunedMerklePaths<PF<EF>, PF<EF>>>,
}

impl<EF: KoalaBearExtension, P: Permutation<[PF<EF>; WIDTH]>> ProverState<EF, P> {
    #[must_use]
    pub fn new(permutation: P, capacity: [PF<EF>; CAPACITY]) -> Self {
        assert!(EF::DIMENSION <= RATE);
        Self {
            challenger: Challenger::new(permutation, capacity),
            transcript: Vec::new(),
            merkle_paths: Vec::new(),
        }
    }

    pub fn into_proof(self) -> Proof<PF<EF>> {
        Proof {
            transcript: self.transcript,
            merkle_paths: self.merkle_paths,
        }
    }
}

impl<EF: KoalaBearExtension, P: Permutation<[PF<EF>; WIDTH]>> ChallengeSampler<EF> for ProverState<EF, P> {
    fn sample_vec(&mut self, len: usize) -> Vec<EF> {
        sample_vec(&mut self.challenger, len)
    }

    fn sample_in_range(&mut self, bits: usize, n_samples: usize) -> Vec<usize> {
        self.challenger.sample_in_range(bits, n_samples)
    }
}

impl<EF: KoalaBearExtension, P: Permutation<[PF<EF>; WIDTH]> + Permutation<[<PF<EF> as Field>::Packing; WIDTH]>>
    FSProver<EF> for ProverState<EF, P>
{
    fn add_base_scalars(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_many(scalars);
        self.transcript.extend_from_slice(scalars);
    }

    fn observe_scalars(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_many(scalars);
    }

    fn duplex(&mut self) {
        self.challenger.duplex();
    }

    fn state(&self) -> String {
        format!(
            "state: {} (n_items: {})",
            self.challenger
                .state
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.transcript.len()
        )
    }

    fn add_sumcheck_polynomial(&mut self, coeffs: &[EF], eq_alpha: Option<EF>) {
        match eq_alpha {
            None => {
                let scalars = flatten_scalars_to_base(coeffs);
                self.challenger.observe_many(&scalars);
                self.transcript.extend_from_slice(&scalars[EF::DIMENSION..]); // c0 reconstructed by verifier from claimed_sum
            }
            Some(alpha) => {
                let bare_scalars = flatten_scalars_to_base(coeffs);
                let full_scalars = flatten_scalars_to_base(&expand_bare_to_full(coeffs, alpha));
                self.challenger.observe_many(&full_scalars);
                self.transcript.extend_from_slice(&bare_scalars[EF::DIMENSION..]); // h0 reconstructed by verifier from claimed_sum
            }
        }
    }

    fn hint_merkle_paths_base(&mut self, paths: Vec<MerklePath<PF<EF>, PF<EF>>>) {
        self.merkle_paths.push(MerklePaths(paths).prune());
    }

    fn pow_grinding(&mut self, bits: usize) {
        assert!(bits < PF::<EF>::bits());

        if bits == 0 {
            return;
        }

        let time = Instant::now();

        type Packed<EF> = <PF<EF> as Field>::Packing;
        let lanes = Packed::<EF>::WIDTH;

        // Deterministic: the result is the SMALLEST valid nonce, which is what a one-thread search
        // returns. Batches are claimed in increasing order, so once some thread has found a nonce,
        // any batch that starts at or above it cannot improve on it and is skipped, while every batch
        // below it is still searched in full. The verifier accepts any valid nonce; this only removes
        // the run-to-run variation that made proofs differ between otherwise identical runs.
        let num_batches = PF::<EF>::ORDER_U64.div_ceil(lanes as u64);
        let next_batch = AtomicU64::new(0);
        let best = AtomicU64::new(u64::MAX);
        parallel::for_each_index(parallel::num_threads(), |_| {
            loop {
                let batch = next_batch.fetch_add(1, Ordering::Relaxed);
                if batch >= num_batches {
                    return;
                }
                let base = batch * lanes as u64;
                if base >= best.load(Ordering::Relaxed) {
                    return;
                }

                let packed_witnesses = Packed::<EF>::from_fn(|lane| {
                    let candidate = base + lane as u64;
                    assert!(candidate < PF::<EF>::ORDER_U64);
                    unsafe { PF::<EF>::from_canonical_unchecked(candidate) }
                });

                let mut packed_state = [Packed::<EF>::ZERO; WIDTH];
                for (slot, val) in packed_state[..CAPACITY]
                    .iter_mut()
                    .zip(&self.challenger.state[..CAPACITY])
                {
                    *slot = Packed::<EF>::from(*val);
                }
                packed_state[CAPACITY] = packed_witnesses;

                self.challenger.permutation.permute_mut(&mut packed_state);

                let samples = packed_state[CAPACITY].as_slice();
                for (lane, sample) in samples.iter().enumerate() {
                    let rand_usize = sample.as_canonical_u64() as usize;
                    if (rand_usize & ((1 << bits) - 1)) == 0 {
                        best.fetch_min(base + lane as u64, Ordering::Relaxed);
                        return;
                    }
                }
            }
        });
        let best = best.load(Ordering::Relaxed);
        assert!(best != u64::MAX, "failed to find witness");
        let witness = unsafe { PF::<EF>::from_canonical_unchecked(best) };

        self.challenger.observe_many(&[witness]);
        assert!(self.challenger.state[CAPACITY].as_canonical_u64() & ((1 << bits) - 1) == 0);
        self.transcript.push(witness);

        let elapsed = time.elapsed();
        POW_GRINDING_NANOS.fetch_add(elapsed.as_nanos() as u64, Ordering::Relaxed);
    }
}
