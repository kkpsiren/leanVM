//! Bytecode representation and management

use backend::*;

use crate::{DIMENSION, F, FileId, FunctionName, Hint, N_INSTRUCTION_COLUMNS, SourceLocation};

use super::Instruction;
use super::encoder::field_representation;
use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};

/// Diagnostic builds only: one host timestamp per phase, never per instruction/hash round.
#[inline]
pub fn init_profile_mark(phase: u32) {
    #[cfg(all(feature = "init-profile", target_arch = "wasm32"))]
    {
        #[link(wasm_import_module = "fb_profile")]
        unsafe extern "C" { fn mark(phase: u32); }
        unsafe { mark(phase); }
    }
    #[cfg(all(feature = "init-profile", not(target_arch = "wasm32")))]
    {
        static START: std::sync::OnceLock<std::time::Instant> = std::sync::OnceLock::new();
        let start = START.get_or_init(std::time::Instant::now);
        eprintln!("init_profile {phase} {:.6}", start.elapsed().as_secs_f64() * 1000.0);
    }
    #[cfg(not(feature = "init-profile"))]
    let _ = phase;
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct CodeEntry {
    pub hints: Box<[Hint]>, // executed before the instruction
    pub instruction: Instruction,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BytecodeDebugInfo {
    pub function_locations: BTreeMap<SourceLocation, FunctionName>,
    pub filepaths: BTreeMap<FileId, String>,
    pub source_code: BTreeMap<FileId, String>,
    /// Maps each pc to its source location
    pub pc_to_location: Vec<SourceLocation>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct BytecodeCacheParts {
    pub code: Vec<CodeEntry>,
    pub unpadded_size: usize,
    pub starting_frame_memory: usize,
    pub hint_name_to_index: BTreeMap<String, usize>,
    pub debug_info: BytecodeDebugInfo,
}

/// The table and ending PC are derived from `code`. Its hash is computed at initialization,
/// or bound by an authenticated release cache whose table-to-hash linkage was audited offline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bytecode {
    unpadded_size: usize,
    code: Vec<CodeEntry>,
    hint_name_to_index: BTreeMap<String, usize>,
    instructions_multilinear: Vec<F>,
    starting_frame_memory: usize,
    ending_pc: usize, // always `code.len() - 1`
    hash: [F; DIGEST_ELEMS],
    debug_info: BytecodeDebugInfo,
}

impl Bytecode {
    pub fn new(
        code: Vec<CodeEntry>,
        unpadded_size: usize,
        starting_frame_memory: usize,
        hint_name_to_index: BTreeMap<String, usize>,
        debug_info: BytecodeDebugInfo,
    ) -> Self {
        Self::new_with_hash(code, unpadded_size, starting_frame_memory, hint_name_to_index, debug_info, None)
    }

    fn new_with_hash(
        code: Vec<CodeEntry>,
        unpadded_size: usize,
        starting_frame_memory: usize,
        hint_name_to_index: BTreeMap<String, usize>,
        debug_info: BytecodeDebugInfo,
        trusted_hash: Option<[F; DIGEST_ELEMS]>,
    ) -> Self {
        assert!(
            code.len().is_power_of_two(),
            "bytecode must be padded to a power of two"
        );
        assert!(unpadded_size <= code.len());
        assert_eq!(debug_info.pc_to_location.len(), code.len());

        init_profile_mark(2);
        let encoded: Vec<[F; N_INSTRUCTION_COLUMNS]> =
            parallel::par_map_collect(code.len(), |i| field_representation(&code[i].instruction));
        init_profile_mark(3);
        let row_width = N_INSTRUCTION_COLUMNS.next_power_of_two();
        let mut instructions_multilinear = F::zero_vec(code.len() * row_width);
        for (row, fields) in instructions_multilinear.chunks_exact_mut(row_width).zip(&encoded) {
            row[..N_INSTRUCTION_COLUMNS].copy_from_slice(fields);
        }
        init_profile_mark(4);
        let hash = trusted_hash.unwrap_or_else(|| poseidon_hash_slice(&instructions_multilinear));
        init_profile_mark(5);
        let ending_pc = code.len() - 1;

        Self {
            unpadded_size,
            code,
            hint_name_to_index,
            instructions_multilinear,
            starting_frame_memory,
            ending_pc,
            hash,
            debug_info,
        }
    }

    /// Number of instructions before padding to a power of two.
    #[inline]
    /// The constructor inputs, for a disk cache (`Bytecode::new` recomputes the multilinear and the
    /// hash on load, so a cache can only cost time, never change what is verified).
    pub fn cache_parts(&self) -> BytecodeCacheParts {
        BytecodeCacheParts { code: self.code.clone(), unpadded_size: self.unpadded_size, starting_frame_memory: self.starting_frame_memory, hint_name_to_index: self.hint_name_to_index.clone(), debug_info: self.debug_info.clone() }
    }
    pub fn from_cache_parts(p: BytecodeCacheParts) -> Self {
        Self::new(p.code, p.unpadded_size, p.starting_frame_memory, p.hint_name_to_index, p.debug_info)
    }

    /// For authenticated release caches only. The caller must authenticate the exact serialized
    /// parts against a trusted release digest and audit their table's linkage to `hash` offline.
    /// Neither pin may come from the cache or an untrusted manifest. General/untrusted caches
    /// must use `from_cache_parts`, which computes the Poseidon hash instead of trusting it.
    /// This still derives every instruction-table cell and retains all execution/debug records.
    pub fn from_cache_parts_with_trusted_hash(p: BytecodeCacheParts, hash: [F; DIGEST_ELEMS]) -> Self {
        Self::new_with_hash(p.code, p.unpadded_size, p.starting_frame_memory,
            p.hint_name_to_index, p.debug_info, Some(hash))
    }

    pub fn unpadded_size(&self) -> usize {
        self.unpadded_size
    }

    #[inline]
    pub fn code(&self) -> &[CodeEntry] {
        &self.code
    }

    #[inline]
    pub fn instructions_multilinear(&self) -> &[F] {
        &self.instructions_multilinear
    }

    #[inline]
    pub fn starting_frame_memory(&self) -> usize {
        self.starting_frame_memory
    }

    #[inline]
    pub fn ending_pc(&self) -> usize {
        self.ending_pc
    }

    /// Poseidon (sponge) hash of `instructions_multilinear`; binds the Fiat-Shamir transcript to the program.
    #[inline]
    pub fn hash(&self) -> &[F; DIGEST_ELEMS] {
        &self.hash
    }

    #[inline]
    pub fn n_hint_slots(&self) -> usize {
        self.hint_name_to_index.len()
    }

    #[inline]
    pub fn debug_info(&self) -> &BytecodeDebugInfo {
        &self.debug_info
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.code.len()
    }

    pub fn padded_size(&self) -> usize {
        self.size().next_power_of_two()
    }

    pub fn log_size(&self) -> usize {
        log2_ceil_usize(self.size())
    }

    pub fn hint_slot(&self, name: &str) -> usize {
        *self
            .hint_name_to_index
            .get(name)
            .unwrap_or_else(|| panic!("hint '{name}' is not declared by the program"))
    }

    pub fn cumulated_n_vars(&self) -> usize {
        self.log_size() + log2_ceil_usize(N_INSTRUCTION_COLUMNS)
    }

    pub fn bytecode_claim_size(&self) -> usize {
        (self.cumulated_n_vars() + 1) * DIMENSION
    }
}

impl Display for Bytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (pc, entry) in self.code.iter().enumerate() {
            for hint in entry.hints.iter() {
                if !matches!(hint, Hint::LocationReport { .. }) {
                    writeln!(f, "hint: {hint}")?;
                }
            }
            writeln!(f, "{pc:>4}: {}", entry.instruction)?;
        }
        Ok(())
    }
}
