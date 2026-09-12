//! Trusted release binding for a FULL instruction cache, including CodeEntry, hints and debug
//! records. The format is the existing postcard cache. The release audit must independently
//! recompute its table's Poseidon hash before this SHA-512 pin is published.
use backend::PrimeCharacteristicRing;
use lean_vm::{Bytecode, BytecodeCacheParts, F};
use lean_vm::ed25519::sha512_table::sha512_bytes;
use crate::verifier_artifact::VK_HASH;

pub const PROVER_CACHE_FILENAME: &str = "prover-bytecode-v1.bin";
pub const MAX_PROVER_CACHE_BYTES: usize = 32 * 1024 * 1024;

// SHA-512 of the deterministic full cache compiled from this crate's embedded zkDSL sources by
// `prepare-prover-cache` (2026-09-12); `audit-prover-cache` re-derives its Poseidon VK independently.
// No supplied hash or manifest is trusted.
pub const PROVER_CACHE_SHA512: [u8; 64] = [
    47, 2, 139, 231, 239, 235, 245, 219, 143, 160, 191, 109, 211, 158, 155, 103,
    157, 2, 218, 182, 32, 64, 76, 58, 35, 200, 209, 162, 12, 84, 109, 194,
    234, 90, 38, 157, 56, 150, 75, 241, 53, 31, 185, 187, 211, 189, 131, 72,
    65, 41, 18, 62, 187, 137, 16, 123, 27, 127, 233, 126, 14, 51, 152, 52,
];

/// Authenticate before postcard sees any file-controlled lengths, then derive the dense table
/// without recomputing Poseidon. Its stored hash is the original VK, not the SHA-512 digest.
pub fn load_prover_cache(bytes: &[u8]) -> Result<Bytecode, String> {
    load_with_pin(bytes, &PROVER_CACHE_SHA512, VK_HASH, 1 << 20)
}

fn load_with_pin(bytes: &[u8], digest: &[u8; 64], hash: [u32; 8], rows: usize) -> Result<Bytecode, String> {
    if bytes.is_empty() || bytes.len() > MAX_PROVER_CACHE_BYTES { return Err("prover cache size".into()); }
    if sha512_bytes(bytes) != *digest { return Err("prover cache digest differs from release pin".into()); }
    let (parts, rest) = postcard::take_from_bytes::<BytecodeCacheParts>(bytes)
        .map_err(|e| format!("prover cache: {e}"))?;
    if !rest.is_empty() || parts.code.len() != rows || !rows.is_power_of_two()
        || parts.unpadded_size > rows || parts.debug_info.pc_to_location.len() != rows {
        return Err("invalid prover cache dimensions or trailing bytes".into());
    }
    Ok(Bytecode::from_cache_parts_with_trusted_hash(parts, hash.map(F::from_u32)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::PrimeField32;
    use lean_vm::{BytecodeDebugInfo, CodeEntry, Instruction, MemOrConstant, MemOrFpOrConstant, Operation, SourceLocation};

    fn fixture() -> Bytecode {
        let code = vec![CodeEntry {
            hints: Box::new([]),
            instruction: Instruction::Computation {
                operation: Operation::Add,
                arg_a: MemOrConstant::zero(), arg_c: MemOrFpOrConstant::Constant(F::ZERO),
                res: MemOrConstant::zero(),
            },
        }; 8];
        Bytecode::new(code, 7, 16, Default::default(), BytecodeDebugInfo {
            pc_to_location: vec![SourceLocation { file_id: 0, line_number: 1 }; 8],
            ..Default::default()
        })
    }

    #[test]
    fn authenticated_cache_equivalence_and_tamper_rejection() {
        let original = fixture();
        let bytes = postcard::to_allocvec(&original.cache_parts()).unwrap();
        let digest = sha512_bytes(&bytes);
        let hash = original.hash().map(|f| f.as_canonical_u32());
        assert_eq!(load_with_pin(&bytes, &digest, hash, 8).unwrap(), original);
        // Every byte is covered, including hints/debug metadata that the table hash does not bind.
        for i in 0..bytes.len() {
            let mut bad = bytes.clone(); bad[i] ^= 1;
            assert!(load_with_pin(&bad, &digest, hash, 8).unwrap_err().contains("digest"));
        }
        for end in 0..bytes.len() { assert!(load_with_pin(&bytes[..end], &digest, hash, 8).is_err()); }
        let mut trailing = bytes.clone(); trailing.push(0);
        assert!(load_with_pin(&trailing, &digest, hash, 8).is_err());
        // Even an authenticated payload must pass the structural checks. These test pins are
        // local to this unit test; production callers cannot supply or replace the release pin.
        assert!(load_with_pin(&trailing, &sha512_bytes(&trailing), hash, 8).is_err());
        assert!(load_with_pin(&bytes, &digest, hash, 16).is_err());
        for damage in 0..3 {
            let mut parts = original.cache_parts();
            match damage {
                0 => { parts.code.pop(); },
                1 => parts.unpadded_size = 9,
                _ => { parts.debug_info.pc_to_location.pop(); },
            }
            let bad = postcard::to_allocvec(&parts).unwrap();
            assert!(load_with_pin(&bad, &sha512_bytes(&bad), hash, 8).is_err());
        }
        assert!(load_prover_cache(&bytes).is_err(), "a fixture digest is not a trusted release");
        assert!(load_with_pin(&[255; 16], &sha512_bytes(&[255; 16]), hash, 8).is_err());
    }
}
