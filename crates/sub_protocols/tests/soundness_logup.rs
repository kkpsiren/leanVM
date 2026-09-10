use backend::{Field, PrimeField64, log2_ceil_usize};
use lean_prover::{SECURITY_BITS, WHIR_SECURITY_BITS, default_whir_config};
use lean_vm::{
    DIMENSION, EF, F, LOG_MAX_BUS_WIDTH, MAX_BYTECODE_LOG_SIZE, MAX_LOG_MEMORY_SIZE,
    MAX_LOG_N_ROWS_PER_TABLE, sort_tables_by_height,
};
use std::collections::BTreeMap;
use sub_protocols::{compute_total_logup_length, compute_total_logup_log_size};

// floor(|EF| / 2^bits), using exact integer arithmetic and no new dependency.
// For our quintic extension: p^5 = p^3 * p^2. Compute p^5 >> 64 without
// ever constructing the full 155-bit integer in a u128.
fn field_order_shifted(bits: usize) -> u128 {
    assert_eq!(DIMENSION, 5);
    assert!((64..192).contains(&bits));
    let p = u128::from(F::ORDER_U64);
    let p2 = p * p;
    let p3 = p2 * p;
    let high = (p3 >> 64) * p2 + ((u128::from(p3 as u64) * p2) >> 64);
    high >> (bits - 64)
}

#[test]
fn ensure_logup_soundness_is_sufficient() {
    let heights = sort_tables_by_height(&BTreeMap::from(MAX_LOG_N_ROWS_PER_TABLE));
    let n = compute_total_logup_length(MAX_LOG_MEMORY_SIZE, MAX_BYTECODE_LOG_SIZE, &heights);
    let n_vars = compute_total_logup_log_size(MAX_LOG_MEMORY_SIZE, MAX_BYTECODE_LOG_SIZE, &heights);
    assert_eq!(log2_ceil_usize(n), n_vars);

    // Each tuple fingerprint is multilinear in LOG_MAX_BUS_WIDTH independent
    // challenges. A denominator c - fp(tuple) has total degree at most that width
    // (or 1 for c). Clearing N denominators from sum_i m_i/(c - fp_i) gives a
    // numerator of degree <= max(1, width)*(N-1). Distinct tuple fingerprints are
    // distinct polynomials; nonzero net multiplicities give a nonzero rational
    // identity. The VM's separate no-overflow check is required for that premise.
    // Schwartz-Zippel bounds this identity-test term by degree/|EF|, assuming
    // independent uniform challenges. This does not account anew for PCS/GKR,
    // Fiat-Shamir, hashing or recursive composition. Padding only loosens N.
    let degree = LOG_MAX_BUS_WIDTH.max(1) as u128 * (n - 1) as u128;
    let bits = DIMENSION as f64 * (F::ORDER_U64 as f64).log2() - (degree as f64).log2();
    println!("LogUp slots={n}, padded_n_vars={n_vars}, degree={degree}, field_bit_length={}, bound_bits={bits:.9}, declared_bits={SECURITY_BITS}, WHIR_target={WHIR_SECURITY_BITS}", EF::bits());
    // EF::bits() is ceil(log2(|EF|)), not field entropy. Compare exactly;
    // the printed floating-point value is diagnostic, never the assertion.
    assert!(degree <= field_order_shifted(SECURITY_BITS));
    assert!(WHIR_SECURITY_BITS >= SECURITY_BITS);
}

#[test]
fn field_order_bound_and_existing_whir_target() {
    // Independently computed with Python integer arithmetic: p**5 >> bits.
    assert_eq!(field_order_shifted(123), 4_129_796_185);
    assert_eq!(field_order_shifted(124), 2_064_898_092);
    // Lowering the declared LogUp budget must not lower WHIR queries or change
    // existing proof/VK compatibility.
    for rate in 1..=4 {
        assert_eq!(default_whir_config(rate).security_level, 124);
    }
}
