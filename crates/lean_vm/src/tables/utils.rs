use backend::*;

use crate::ExtraDataForBuses;

/// Bus "fingerprint" over the logup randomness: `Σ alphas[i]·data[i] + alphas_last·domainsep`.
///
/// The AIR sumcheck now emits this and `multiplicity` as two separate constraints
/// (consuming `alpha^0` and `alpha^1`), so the AIR's batching alpha takes over the
/// role that the previous separate `bus_beta` played as a random combiner. Callers
/// emit this via `assert_zero_ef` (or `assert_zero_linear` for an EF-typed linear
/// expression if a future linear-EF builder method is added).
pub fn bus_fingerprint<AB: AirBuilder, EF: ExtensionField<PF<EF>>>(
    extra_data: &ExtraDataForBuses<EF>,
    domainsep: AB::IF,
    data: &[AB::IF],
) -> AB::EF {
    let logup_alphas_eq_poly = extra_data.transmute_bus_data::<AB::EF>();

    assert!(data.len() < logup_alphas_eq_poly.len());
    logup_alphas_eq_poly
        .iter()
        .zip(data)
        .map(|(c, d)| *c * *d)
        .sum::<AB::EF>()
        + *logup_alphas_eq_poly.last().unwrap() * domainsep
}
