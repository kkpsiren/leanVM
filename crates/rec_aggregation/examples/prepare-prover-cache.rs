//! One-time, explicit preparation of the release prover cache (`PROVER_CACHE_FILENAME`).
//! Compiles the recursion bytecode from the embedded zkDSL sources, serializes the full cache,
//! requires its Poseidon table hash to equal the release VK and its SHA-512 to equal the release
//! pin, re-loads it through the production authenticated loader, then installs it atomically.
//! Ordinary proving never compiles: `init_aggregation_bytecode_cached` only loads this file.
use backend::PrimeField32;
use lean_vm::ed25519::sha512_table::sha512_bytes;
use rec_aggregation::{get_aggregation_bytecode, init_aggregation_bytecode,
    prover_artifact::{load_prover_cache, PROVER_CACHE_FILENAME, PROVER_CACHE_SHA512}, verifier_artifact::VK_HASH};

fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 2, "usage: prepare-prover-cache CACHE_DIR");
    let dir = std::path::Path::new(&args[1]);
    let target = dir.join(PROVER_CACHE_FILENAME);
    if let Ok(existing) = std::fs::read(&target) {
        if load_prover_cache(&existing).is_ok() {
            println!("{}", serde_json::json!({"status": "pass", "path": target.display().to_string(), "bytes": existing.len(), "note": "already holds the authenticated release cache"}));
            return;
        }
        eprintln!("existing {} does not authenticate; it will be replaced", target.display());
    }
    let start = std::time::Instant::now();
    init_aggregation_bytecode();
    let bytecode = get_aggregation_bytecode();
    let compile_s = start.elapsed().as_secs_f64();
    assert_eq!(bytecode.hash().map(|f| f.as_canonical_u32()), VK_HASH, "compiled instruction table does not hash to the release VK");
    let bytes = postcard::to_allocvec(&bytecode.cache_parts()).expect("serialize the full cache");
    let digest = sha512_bytes(&bytes);
    if digest != PROVER_CACHE_SHA512 {
        eprintln!("FAIL: compiled cache sha512 {} differs from the release pin {}; nothing written", hex(&digest), hex(&PROVER_CACHE_SHA512));
        std::process::exit(2);
    }
    let reloaded = load_prover_cache(&bytes).expect("authenticated reload of the freshly compiled cache");
    assert_eq!(&reloaded, bytecode, "the authenticated loader must reproduce the compiled bytecode exactly");
    std::fs::create_dir_all(dir).expect("create the cache directory");
    let tmp = target.with_extension("tmp");
    std::fs::write(&tmp, &bytes).expect("write the cache");
    std::fs::rename(&tmp, &target).expect("install the cache");
    println!("{}", serde_json::json!({"status": "pass", "path": target.display().to_string(), "bytes": bytes.len(), "sha512": hex(&digest), "compile_s": compile_s}));
}
