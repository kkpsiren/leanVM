use backend::*;
use rand::{CryptoRng, RngExt};
use serde::{Deserialize, Serialize};

use crate::*;

#[derive(Debug)]
pub struct WotsSecretKey {
    pub pre_images: [Digest; V],
    public_key: WotsPublicKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WotsPublicKey(pub [Digest; V]);

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WotsSignature {
    #[serde(
        with = "backend::array_serialization",
        bound(serialize = "F: Serialize", deserialize = "F: Deserialize<'de>")
    )]
    pub chain_tips: [Digest; V],
    pub randomness: Randomness,
}

impl WotsSecretKey {
    pub fn random(rng: &mut impl CryptoRng, public_param: PublicParam, slot: u32) -> Self {
        Self::new(rng.random(), public_param, slot)
    }

    pub fn new(pre_images: [Digest; V], public_param: PublicParam, slot: u32) -> Self {
        Self {
            pre_images,
            public_key: WotsPublicKey(std::array::from_fn(|i| {
                iterate_hash(&pre_images[i], CHAIN_LENGTH - 1, public_param, slot, i, 0)
            })),
        }
    }

    pub const fn public_key(&self) -> &WotsPublicKey {
        &self.public_key
    }

    pub fn sign_with_randomness(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        xmss_pub_key: &XmssPublicKey,
        randomness: Randomness,
    ) -> Option<WotsSignature> {
        let encoding = wots_encode(message, slot, xmss_pub_key, &randomness)?;
        Some(self.sign_with_encoding(randomness, &encoding, xmss_pub_key.public_param, slot))
    }

    fn sign_with_encoding(
        &self,
        randomness: Randomness,
        encoding: &[u8; V],
        public_param: PublicParam,
        slot: u32,
    ) -> WotsSignature {
        WotsSignature {
            chain_tips: std::array::from_fn(|i| {
                iterate_hash(&self.pre_images[i], encoding[i] as usize, public_param, slot, i, 0)
            }),
            randomness,
        }
    }
}

impl WotsSignature {
    pub fn recover_public_key(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        xmss_pub_key: &XmssPublicKey,
    ) -> Option<WotsPublicKey> {
        let encoding = wots_encode(message, slot, xmss_pub_key, &self.randomness)?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash(
                &self.chain_tips[i],
                CHAIN_LENGTH - 1 - encoding[i] as usize,
                xmss_pub_key.public_param,
                slot,
                i,
                encoding[i] as usize,
            )
        })))
    }
}

impl WotsPublicKey {
    // Overwrite-sponge
    pub fn hash(&self, public_param: PublicParam, slot: u32) -> Digest {
        // state[0..4] = IV [tweak(1) | 0 | pp(2)]; state[4..8] = 0.
        let mut state = [F::ZERO; WIDTH];
        state[..TWEAK_LEN].copy_from_slice(&make_tweak(TWEAK_TYPE_WOTS_PK, 0, slot));
        state[2..2 + PUBLIC_PARAM_LEN_FE].copy_from_slice(&public_param);
        state = poseidon8_permute(state);
        for i in (0..V).step_by(2) {
            state[CAPACITY..][..XMSS_DIGEST_LEN].copy_from_slice(&self.0[i]);
            state[CAPACITY + XMSS_DIGEST_LEN..].copy_from_slice(&self.0[i + 1]);
            state = poseidon8_permute(state);
        }
        state[CAPACITY..][..XMSS_DIGEST_LEN].try_into().unwrap()
    }
}

pub fn iterate_hash(
    a: &Digest,
    n: usize,
    public_param: PublicParam,
    slot: u32,
    chain_index: usize,
    start_step: usize,
) -> Digest {
    // Chain hash layout: left = [tweak (1) | zero (1) | data (2)], right = [public_param(2) | zeros(2)].
    let right = build_right_chain_input(&public_param);
    (0..n).fold(*a, |acc, j| {
        let tweak = make_tweak(TWEAK_TYPE_CHAIN, chain_index * CHAIN_LENGTH + start_step + j, slot);
        let left = build_left_chain_input(tweak, &acc);
        poseidon8_compress_pair(&left, &right)[..XMSS_DIGEST_LEN]
            .try_into()
            .unwrap()
    })
}

pub fn find_randomness_for_wots_encoding(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    xmss_pub_key: &XmssPublicKey,
    rng: &mut impl CryptoRng,
) -> (Randomness, [u8; V], usize) {
    let mut num_iters = 0;
    loop {
        num_iters += 1;
        let randomness = rng.random();
        if let Some(encoding) = wots_encode(message, slot, xmss_pub_key, &randomness) {
            return (randomness, encoding, num_iters);
        }
    }
}

pub fn wots_encode(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    xmss_pub_key: &XmssPublicKey,
    randomness: &Randomness,
) -> Option<[u8; V]> {
    let first_input_left = message;
    let mut first_input_right = [F::default(); DIGEST_LEN_FE];
    first_input_right[..RANDOMNESS_LEN_FE].copy_from_slice(randomness);
    first_input_right[RANDOMNESS_LEN_FE..][..TWEAK_LEN].copy_from_slice(&make_tweak(TWEAK_TYPE_ENCODING, 0, slot));
    let pre_compressed = poseidon8_compress_pair(first_input_left, &first_input_right);

    let mut second_input_right = [F::default(); DIGEST_LEN_FE];
    second_input_right[..PUBLIC_PARAM_LEN_FE].copy_from_slice(&xmss_pub_key.public_param);
    let compressed = poseidon8_compress_pair(&pre_compressed, &second_input_right);

    // Per-FE decomposition: each output FE contributes V/DIGEST_LEN_FE
    // = 10 W-bit chunks from the low 30 bits of its low limb; the top 2 bits
    // of each FE's low limb must be zero (ENCODING_NUM_FINAL_ZEROS = 8 bits
    // total, evenly distributed = 2 per FE)
    const CHUNKS_PER_FE: usize = V / DIGEST_LEN_FE;
    const CHUNK_BITS_PER_FE: usize = CHUNKS_PER_FE * W;
    let mut all_indices = [0u8; V];
    for (i, fe) in compressed.iter().enumerate() {
        let low = fe.as_canonical_u64() & ((1u64 << 32) - 1);
        if (low >> CHUNK_BITS_PER_FE) != 0 {
            return None;
        }
        for j in 0..CHUNKS_PER_FE {
            all_indices[i * CHUNKS_PER_FE + j] = ((low >> (W * j)) & ((1u64 << W) - 1)) as u8;
        }
    }
    is_valid_encoding(&all_indices).then_some(all_indices)
}

fn is_valid_encoding(encoding: &[u8]) -> bool {
    if encoding.len() != V {
        return false;
    }
    if !encoding.iter().all(|&x| (x as usize) < CHAIN_LENGTH) {
        return false;
    }
    if encoding.iter().map(|&x| x as usize).sum::<usize>() != TARGET_SUM {
        return false;
    }
    true
}
