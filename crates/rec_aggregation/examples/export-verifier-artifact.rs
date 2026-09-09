//! Offline release linkage audit. Reads an existing cache; no compiler/prover or new proof.
use backend::*;
use lean_vm::{Bytecode, BytecodeCacheParts, DictionaryProgram, VerifierProgram, EF, F};
use lean_vm::ed25519::sha512_table::sha512_bytes;
use rec_aggregation::verifier_artifact::{ARTIFACT_SHA512, VK_HASH};

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert!(args.len() == 3 || args.len() == 4, "usage: existing-cache.bin output-vk.bin [--check-pin]");
    if args.len() == 4 { assert_eq!(args[3], "--check-pin"); }
    let bytes = std::fs::read(&args[1]).unwrap();
    let (parts, rest): (BytecodeCacheParts, _) = postcard::take_from_bytes(&bytes).unwrap();
    assert!(rest.is_empty());
    assert_eq!(parts.code.len(), 1 << 20);
    let bc = Bytecode::from_cache_parts(parts);
    assert_eq!(bc.hash().map(|f| f.as_canonical_u32()), VK_HASH, "original cache must match the trusted VK");
    let encoded = DictionaryProgram::encode_bytecode(&bc);
    let digest = sha512_bytes(&encoded);
    let compact = DictionaryProgram::from_pinned_bytes(&encoded, &digest, VK_HASH).unwrap();
    // An actual second Poseidon computation over the DECODED artifact, not its embedded hash.
    let expanded = compact.expand_for_audit();
    assert_eq!(expanded, bc.instructions_multilinear(), "every decoded field must agree");
    assert_eq!(poseidon_hash_slice(&expanded).map(|f| f.as_canonical_u32()), VK_HASH);
    assert_eq!(compact.log_size(), bc.log_size());
    assert_eq!(compact.ending_pc(), bc.ending_pc());
    for seed in 0..4 {
        let point = MultilinearPoint((0..bc.cumulated_n_vars()).map(|i| {
            if seed == 0 { EF::ZERO } else {
                EF::from_basis_coefficients_slice(&(0..5).map(|j| F::from_usize(1 + seed * 97 + i * 11 + j * 31)).collect::<Vec<_>>()).unwrap()
            }
        }).collect());
        assert_eq!(compact.evaluate(&point), VerifierProgram::evaluate(&bc, &point), "real table evaluation seed {seed}");
    }
    if args.len() == 4 { assert_eq!(digest, ARTIFACT_SHA512, "checked-in release pin"); }
    std::fs::write(&args[2], &encoded).unwrap();
    println!("bytes={} sha512={}", encoded.len(), digest.iter().map(|b| format!("{b:02x}")).collect::<String>());
    println!("rust_pin={digest:?}");
    println!("PASS: source Poseidon pin, all 16777216 decoded cells, decoded Poseidon pin, four dense/dictionary extension-field evaluations");
}
