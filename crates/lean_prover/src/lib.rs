#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use std::fmt::Display;

pub mod ed25519_leaf;
pub mod prove_execution;
/// Witness/trace construction exposed for diagnostics that must not allocate PCS or GKR buffers.
pub mod trace_gen;
pub mod verify_execution;

use backend::*;
use lean_vm::*;
#[cfg(test)]
mod test_zkvm;

use trace_gen::*;

// Declared LogUp budget at the supported table maxima. The exact fraction count gives
// 123.46 bits for that term; see sub_protocols/tests/soundness_logup.rs. This is a
// component budget, not a new composition/Fiat-Shamir security proof.
pub const SECURITY_BITS: usize = 123;
// Preserve the existing WHIR parameters and all recursive proofs/VK artifacts. Reducing
// this target would change query counts and require regenerated recursion bytecode/pins.
pub const WHIR_SECURITY_BITS: usize = 124;
/// Exposed so a release consumer can reject this feature even when enabled transitively.
pub const PROX_GAPS_CONJECTURE: bool = cfg!(feature = "prox-gaps-conjecture");

pub const GRINDING_BITS: usize = 16;
pub const MAX_NUM_VARIABLES_TO_SEND_COEFFS: usize = 8;
pub const WHIR_INITIAL_FOLDING_FACTOR: usize = 7;
pub const WHIR_SUBSEQUENT_FOLDING_FACTOR: usize = 5;
pub const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = 5;

pub const SNARK_DOMAIN_SEP: [F; 8] = F::new_array([
    130704175, 1303721200, 493664240, 1035493700, 2063844858, 1410214009, 1938905908, 1696767928,
]);

pub fn fiat_shamir_domain_sep(bytecode: &dyn VerifierProgram) -> [F; 8] {
    poseidon16_compress_pair(bytecode.hash(), &SNARK_DOMAIN_SEP)
}

/// The domain separator of a proof under `profile`: the full profile keeps the historical value;
/// any other profile mixes its id in, so a transcript of one profile cannot be re-parsed as another
/// (the dims header length is the only structural difference between them).
pub fn fiat_shamir_domain_sep_for(bytecode: &dyn VerifierProgram, profile: &Profile) -> [F; 8] {
    let base = fiat_shamir_domain_sep(bytecode);
    if profile.id == 0 { return base; }
    let mut tag = [F::ZERO; 8];
    tag[0] = F::from_u32(profile.id);
    tag[1] = F::from_usize(profile.tables.len());
    poseidon16_compress_pair(&base, &tag)
}

pub fn default_whir_config(starting_log_inv_rate: usize) -> WhirConfigBuilder {
    assert!(0 < starting_log_inv_rate);
    assert!(starting_log_inv_rate <= MAX_WHIR_LOG_INV_RATE);
    WhirConfigBuilder {
        folding_factor: FoldingFactor::new(WHIR_INITIAL_FOLDING_FACTOR, WHIR_SUBSEQUENT_FOLDING_FACTOR),
        soundness_type: if PROX_GAPS_CONJECTURE {
            SecurityAssumption::CapacityBound // TODO update formula with State of the Art Conjecture
        } else {
            SecurityAssumption::JohnsonBound
        },
        pow_bits: GRINDING_BITS,
        max_num_variables_to_send_coeffs: MAX_NUM_VARIABLES_TO_SEND_COEFFS,
        rs_domain_initial_reduction_factor: RS_DOMAIN_INITIAL_REDUCTION_FACTOR,
        security_level: WHIR_SECURITY_BITS,
        starting_log_inv_rate,
    }
}

pub(crate) fn check_rate(log_inv_rate: usize) -> Result<(), ProofError> {
    if (MIN_WHIR_LOG_INV_RATE..=MAX_WHIR_LOG_INV_RATE).contains(&log_inv_rate) {
        Ok(())
    } else {
        Err(ProofError::InvalidRate)
    }
}

#[derive(Debug, Clone)]
pub enum ProverError {
    TooBigTable(TooBigTableError),
    Runner(RunnerError),
    InvalidRate,
    /// The execution used a table the profile does not commit to (e.g. an ed25519 precompile in a
    /// terminal-profile proof). Fail loud: dropping the rows would leave an unbalanced LogUp sum.
    TableNotInProfile(Table),
}

impl From<TooBigTableError> for ProverError {
    fn from(err: TooBigTableError) -> Self {
        Self::TooBigTable(err)
    }
}

impl From<RunnerError> for ProverError {
    fn from(err: RunnerError) -> Self {
        Self::Runner(err)
    }
}

impl Display for ProverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooBigTable(e) => write!(f, "{}", e),
            Self::Runner(e) => write!(f, "{}", e),
            Self::InvalidRate => write!(
                f,
                "LeanVM supports rate 1/2, 1/4, 1/8 and 1/16 (log_inv_rate in {{1, 2, 3, 4}})"
            ),
            Self::TableNotInProfile(t) => write!(f, "the execution used table {} which the proof profile does not commit to", t.name()),
        }
    }
}

#[cfg(test)]
mod tests {
    use backend::{PrimeCharacteristicRing, default_koalabear_poseidon1_16, hash_slice_rtl, poseidon16_compress_pair};
    use lean_vm::F;
    use rec_aggregation::{get_aggregation_bytecode, init_aggregation_bytecode};

    #[test]
    fn compute_snark_domain_sep() {
        init_aggregation_bytecode();
        let recursion_bytecode_hash = get_aggregation_bytecode().hash();
        let name_fe = "leanVM-0.6.0"
            .as_bytes()
            .iter()
            .map(|b| F::from_u8(*b))
            .collect::<Vec<_>>();
        let mut prefix_free_name_fe = vec![F::ZERO; 8];
        let len = name_fe.len();
        prefix_free_name_fe.extend(name_fe);
        while prefix_free_name_fe.len() % 8 != 7 {
            prefix_free_name_fe.push(F::ZERO);
        }
        prefix_free_name_fe.push(F::from_u64(len as u64));
        let comp = default_koalabear_poseidon1_16();
        let name_hash = hash_slice_rtl::<_, _, _, 8, 8>(&comp, &prefix_free_name_fe);

        // We incorporate the recursion program hash, containing all the verifier logic, into fiat shamir domain separator
        // (likely not necessary but why not, is there a cleaner approach?)
        let domain_sep = poseidon16_compress_pair(&name_hash, recursion_bytecode_hash);

        println!("Computed SNARK_DOMAIN_SEP: {:?}", domain_sep); // We dont assert equality here to avoid the pain of having to update the hardcoded SNARK_DOMAIN_SEP every time we change the recursion program
    }
}
