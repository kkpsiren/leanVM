//! Fresh-process startup measurement, no counting allocator and no proof generation.
//! legacy/release take an existing full cache file; cached takes a directory containing the
//! audited release cache under PROVER_CACHE_FILENAME. Never use cached with an unprepared dir:
//! it exercises the production API, whose normal fallback compiles bytecode.
use backend::PrimeField32;
use lean_vm::{Bytecode, BytecodeCacheParts};
use rec_aggregation::{get_aggregation_bytecode, init_aggregation_bytecode_cached,
    prover_artifact::{load_prover_cache, PROVER_CACHE_FILENAME}, verifier_artifact::VK_HASH};

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 3, "usage: legacy|release|cached FILE_OR_DIRECTORY");
    let start = std::time::Instant::now();
    let owned;
    let bc = match args[1].as_str() {
        "legacy" => {
            let bytes = std::fs::read(&args[2]).unwrap();
            let (parts, rest): (BytecodeCacheParts, _) = postcard::take_from_bytes(&bytes).unwrap();
            assert!(rest.is_empty());
            owned = Bytecode::from_cache_parts(parts);
            &owned
        }
        "release" => {
            owned = load_prover_cache(&std::fs::read(&args[2]).unwrap()).unwrap();
            &owned
        }
        "cached" => {
            let dir = std::path::Path::new(&args[2]);
            assert!(dir.join(PROVER_CACHE_FILENAME).is_file(), "prepare the audited release cache first");
            assert!(init_aggregation_bytecode_cached(dir), "expected an authenticated cache hit");
            get_aggregation_bytecode()
        }
        _ => panic!("unknown mode"),
    };
    let elapsed_s = start.elapsed().as_secs_f64();
    assert_eq!(bc.hash().map(|f| f.as_canonical_u32()), VK_HASH);
    println!("{}", serde_json::json!({"mode": args[1], "startup_s": elapsed_s,
        "instructions": bc.size(), "table_cells": bc.instructions_multilinear().len()}));
}
