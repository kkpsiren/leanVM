//! Release linkage audit for the full prover cache. No compiler, signature witness or proof.
use backend::*;
use lean_vm::{Bytecode, BytecodeCacheParts};
use lean_vm::ed25519::sha512_table::sha512_bytes;
use rec_aggregation::{prover_artifact::{load_prover_cache, PROVER_CACHE_SHA512}, verifier_artifact::VK_HASH};

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 3, "usage: existing-full-cache.bin audited-release-cache.bin");
    let bytes = std::fs::read(&args[1]).unwrap();
    let (parts, rest): (BytecodeCacheParts, _) = postcard::take_from_bytes(&bytes).unwrap();
    assert!(rest.is_empty());
    // The general constructor computes Poseidon independently of the SHA pin / trusted loader.
    let original = Bytecode::from_cache_parts(parts);
    assert_eq!(original.hash().map(|f| f.as_canonical_u32()), VK_HASH);
    let loaded = load_prover_cache(&bytes).unwrap();
    assert_eq!(loaded, original, "all CodeEntry/hint/debug records, dense fields, metadata and hash");
    assert_eq!(postcard::to_allocvec(&loaded.cache_parts()).unwrap(), bytes, "exact full-cache roundtrip");
    assert_eq!(poseidon_hash_slice(loaded.instructions_multilinear()).map(|f| f.as_canonical_u32()), VK_HASH);
    let digest = sha512_bytes(&bytes);
    assert_eq!(digest, PROVER_CACHE_SHA512);
    std::fs::write(&args[2], &bytes).unwrap();
    println!("PASS: independent source and loaded-table Poseidon hashes; every dense field and full execution record; exact serialized roundtrip");
    println!("bytes={} sha512={}", bytes.len(), digest.iter().map(|b| format!("{b:02x}")).collect::<String>());
}
