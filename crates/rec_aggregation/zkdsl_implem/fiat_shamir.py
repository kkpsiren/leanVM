from snark_lib import *
from utils import *


# Duplex-sponge Fiat-Shamir over the Goldilocks width-8 Poseidon permutation.
#
# fs layout (9 cells):
#   fs[0..4]  = capacity
#   fs[4..8]  = rate
#   fs[8]     = transcript pointer
# This matches the natural-ordering poseidon permute precompile output [cap | rate].


@inline
def fs_new(transcript_ptr, initial_capacity):
    fs = Array(9)
    copy_digest(fs, initial_capacity)
    zero_digest(fs + 4)
    fs[8] = transcript_ptr
    return fs


@inline
def _absorb_chunks(fs, data, n_chunks, new_transcript_ptr):
    assert n_chunks != 0
    chain = Array(n_chunks * 8 + 1)
    poseidon8_permute(fs, data, chain)
    for i in unroll(1, n_chunks):
        poseidon8_permute(chain + (i - 1) * 8, data + i * DIGEST_LEN, chain + i * 8)
    chain[n_chunks * 8] = new_transcript_ptr
    return chain + (n_chunks - 1) * 8


@inline
def fs_observe_chunks(fs, data, n_chunks):
    return _absorb_chunks(fs, data, n_chunks, fs[8])


def fs_observe(fs, data, length: Const):
    n_full_chunks = (length - (length % DIGEST_LEN)) / DIGEST_LEN
    remainder = length % DIGEST_LEN
    if remainder == 0:
        return fs_observe_chunks(fs, data, n_full_chunks)
    intermediate = fs_observe_chunks(fs, data, n_full_chunks)
    padded = Array(DIGEST_LEN)
    for j in unroll(0, remainder):
        padded[j] = data[n_full_chunks * DIGEST_LEN + j]
    for j in unroll(remainder, DIGEST_LEN):
        padded[j] = 0
    return fs_observe_chunks(intermediate, padded, 1)


def fs_grinding(fs, bits):
    if bits == 0:
        return fs  # no grinding
    transcript_ptr = fs[8]
    new_fs = _absorb_chunks(fs, transcript_ptr, 1, transcript_ptr + DIGEST_LEN)

    # Rate is at new_fs[4..8]; sample the first cell of it for the grinding check.
    sampled = new_fs[4]
    debug_assert(bits <= 24)
    match_range(bits, range(0, 25), lambda b: assert_trailing_bits_are_zeros(sampled, b))

    return new_fs


def assert_trailing_bits_are_zeros(value, bits: Const):
    debug_assert(bits != 0)
    debug_assert(bits <= 24)

    chunk_size = 16
    num_chunks = F_BITS / chunk_size  # 4
    half_chunks = num_chunks / 2  # 2

    chunks = Array(num_chunks)
    hint_decompose_bits_merkle_whir(chunks, value, num_chunks, chunk_size)
    for i in unroll(0, num_chunks):
        assert chunks[i] < 2**chunk_size

    # Recompose into low/high 32-bit halves and enforce canonicality:
    # if the high 32 bits are all set (top half = 2^32 - 1), the low 32
    # bits must be zero (only valid such element is p - 1 = 2^64 - 2^32).
    partial_sum_low: Mut = chunks[0]
    for i in unroll(1, half_chunks):
        partial_sum_low += chunks[i] * 2 ** (i * chunk_size)
    partial_sum_high: Mut = chunks[half_chunks]
    for i in unroll(1, half_chunks):
        partial_sum_high += chunks[half_chunks + i] * 2 ** (i * chunk_size)

    assert value == partial_sum_low + partial_sum_high * 2**HALF_BITS

    if partial_sum_high == 2**HALF_BITS - 1:
        assert partial_sum_low == 0

    if bits < 16:
        assert chunks[0] / 2**bits < 2 ** (chunk_size - bits)
    else:
        assert chunks[0] == 0
        assert chunks[1] / 2 ** (bits - 16) < 2 ** (chunk_size - (bits - 16))

    return


@inline
def fs_duplex(fs):
    # Equivalent to absorbing DIGEST_LEN zeros.
    # Refreshes the rate so a subsequent sample doesn't repeat the previous one.
    new_fs = Array(9)
    poseidon8_permute(fs, ZERO_VEC_PTR, new_fs)
    new_fs[8] = fs[8]
    return new_fs


def fs_sample_chunks(fs, n_chunks: Const):
    # Returns (new_fs, samples_ptr) where samples_ptr points to a contiguous
    # n_chunks * DIGEST_LEN-cell buffer holding the squeezed chunks. Assumes the
    # rate at fs[4..8] is "fresh" (just-permuted, not yet emitted); caller must
    # duplex (or observe) between independent sample sequences.
    if n_chunks == 0:
        return fs, ZERO_VEC_PTR
    if n_chunks == 1:
        # Chunk 0 is the current fs itself: its rate is fs[4..8], no permute needed.
        return fs, fs + 4
    samples = Array(n_chunks * DIGEST_LEN)
    copy_digest(samples, fs + 4)
    chain = Array((n_chunks - 1) * 8 + 1)
    poseidon8_permute(fs, ZERO_VEC_PTR, chain)
    copy_digest(samples + DIGEST_LEN, chain + 4)
    for i in unroll(2, n_chunks):
        poseidon8_permute(chain + (i - 2) * 8, ZERO_VEC_PTR, chain + (i - 1) * 8)
        copy_digest(samples + i * DIGEST_LEN, chain + (i - 1) * 8 + 4)
    chain[(n_chunks - 1) * 8] = fs[8]
    new_fs = chain + (n_chunks - 2) * 8
    return new_fs, samples


@inline
def fs_sample_ef(fs):
    # Single-chunk sample: read the fresh rate at fs[4..8]; the new fs is unchanged.
    return fs, fs + 4


@inline
def fs_sample_many_ef(fs, n):
    # return the updated fiat-shamir, and a pointer to n (continuous) extension field elements
    n_chunks = div_ceil(n * DIM, DIGEST_LEN)
    debug_assert(n_chunks <= 31)
    debug_assert(1 <= n_chunks)
    new_fs, sampled = fs_sample_chunks(fs, n_chunks)
    return new_fs, sampled


def fs_receive_chunks(fs, n_chunks: Const):
    # Read n_chunks * DIGEST_LEN cells from the transcript and absorb them. Returns the
    # new fs and a pointer to the just-consumed transcript region.
    transcript_ptr = fs[8]
    new_fs = _absorb_chunks(fs, transcript_ptr, n_chunks, transcript_ptr + n_chunks * DIGEST_LEN)
    return new_fs, transcript_ptr


@inline
def fs_receive_ef_inlined(fs, n):
    new_fs, ef_ptr = fs_receive_chunks(fs, div_ceil(n * DIM, DIGEST_LEN))
    for i in unroll(n * DIM, next_multiple_of(n * DIM, DIGEST_LEN)):
        assert ef_ptr[i] == 0
    return new_fs, ef_ptr


def fs_receive_ef_by_log_dynamic(fs, log_n, min_value: Const, max_value: Const):
    debug_assert(log_n < max_value)
    debug_assert(min_value <= log_n)
    new_fs: Imm
    ef_ptr: Imm
    new_fs, ef_ptr = match_range(log_n, range(min_value, max_value), lambda ln: fs_receive_ef(fs, 2**ln))
    return new_fs, ef_ptr


def fs_receive_ef(fs, n: Const):
    new_fs, ef_ptr = fs_receive_chunks(fs, div_ceil(n * DIM, DIGEST_LEN))
    for i in unroll(n * DIM, next_multiple_of(n * DIM, DIGEST_LEN)):
        assert ef_ptr[i] == 0
    return new_fs, ef_ptr


@inline
def fs_sample_queries(fs, n_samples):
    # Sample `n_samples` query bit-strings. Each chunk yields DIGEST_LEN base field
    # elements that can be downsampled to query indices. We squeeze
    # `ceil(n_samples / DIGEST_LEN)` chunks.
    debug_assert(n_samples < 512)
    # total_chunks = ceil(n_samples / DIGEST_LEN). With DIGEST_LEN=4 we shift right
    # by 2 and check whether the low 2 bits are nonzero. BE decomposition:
    # nb[0] = bit 8 (MSB), nb[8] = bit 0 (LSB).
    nb = checked_decompose_bits_small_value_const(n_samples, 9)
    floor_div = nb[0] * 64 + nb[1] * 32 + nb[2] * 16 + nb[3] * 8 + nb[4] * 4 + nb[5] * 2 + nb[6]
    has_remainder = 1 - (1 - nb[7]) * (1 - nb[8])
    total_chunks = floor_div + has_remainder
    new_fs, sampled = match_range(total_chunks, range(0, 129), lambda nc: fs_sample_chunks(fs, nc))
    return sampled, new_fs
