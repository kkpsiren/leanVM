//! Inspect only an existing compiled cache; never compiles bytecode or generates a proof.
use backend::*;
use lean_vm::{Bytecode, BytecodeCacheParts};
use std::collections::HashSet;
fn main() {
    let path = std::env::args().nth(1).expect("existing cache path");
    let bytes = std::fs::read(path).unwrap();
    let (parts, rest): (BytecodeCacheParts, _) = postcard::take_from_bytes(&bytes).unwrap();
    assert!(rest.is_empty());
    let bc = Bytecode::from_cache_parts(parts);
    let table = bc.instructions_multilinear();
    let rows: HashSet<Vec<u32>> = table.chunks_exact(16).map(|r| r.iter().map(|f| f.as_canonical_u32()).collect()).collect();
    let unique: HashSet<u32> = table.iter().map(|f| f.as_canonical_u32()).collect();
    let nonzero = table.iter().filter(|f| !f.is_zero()).count();
    let mut runs = 0;
    for col in 0..16 {
        let mut prev = None;
        for i in (col..table.len()).step_by(16) {
            if prev != Some(table[i]) { runs += 1; }
            prev = Some(table[i]);
        }
    }
    println!("unpadded={} unique_rows={} unique_fields={} nonzero={} column_runs={}", bc.unpadded_size(), rows.len(), unique.len(), nonzero, runs);
}
