//! Strip prover hints/debug metadata from an EXISTING compiled cache. No compiler or prover runs.
//! The result is for verification only; do not use it as a prover cache.
use backend::PrimeField32;
use lean_vm::{Bytecode, BytecodeCacheParts, SourceLocation};
fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert!(args.len() == 3 || args.len() == 4, "usage: input-cache.bin output-cache.bin [wrong-vk-fixture.bin]");
    let bytes = std::fs::read(&args[1]).unwrap();
    let (mut parts, rest): (BytecodeCacheParts, _) = postcard::take_from_bytes(&bytes).unwrap();
    assert!(rest.is_empty());
    assert_eq!(parts.code.len(), 1 << 20);
    for entry in &mut parts.code { entry.hints = Box::new([]); }
    parts.hint_name_to_index.clear();
    parts.debug_info.function_locations.clear();
    parts.debug_info.filepaths.clear();
    parts.debug_info.source_code.clear();
    parts.debug_info.pc_to_location.fill(SourceLocation { file_id: 0, line_number: 0 });
    let output = postcard::to_allocvec(&parts).unwrap();
    let bc = Bytecode::from_cache_parts(parts);
    let expected = [1153961582, 1250141101, 1638904970, 1982146112, 763994888, 2126617202, 1686598344, 1973457087];
    assert_eq!(bc.hash().map(|f| f.as_canonical_u32()), expected);
    std::fs::write(&args[2], &output).unwrap();
    if args.len() == 4 {
        // Optional negative fixture: valid cache framing, a different instruction table.
        let mut wrong = bc.cache_parts();
        let padding = wrong.code.last().unwrap().instruction.clone();
        let entry = wrong.code.iter_mut().find(|e| e.instruction != padding).unwrap();
        entry.instruction = padding;
        let bytes = postcard::to_allocvec(&wrong).unwrap();
        assert_ne!(Bytecode::from_cache_parts(wrong).hash().map(|f| f.as_canonical_u32()), expected);
        std::fs::write(&args[3], bytes).unwrap();
    }
    println!("original={} stripped={} log_size={} variables={} dense_bytes={} hash={expected:?}",
        bytes.len(), output.len(), bc.log_size(), bc.cumulated_n_vars(), bc.instructions_multilinear().len()*4);
}
