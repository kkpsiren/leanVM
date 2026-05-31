//! Deterministic, seedable RNG used by every generator.
//!
//! All randomness in the fuzzer flows through [`Rng`] so that a single `u64` seed fully
//! determines a generated program, its witnesses, and any mutation applied to it. This is
//! what makes findings reproducible: re-running the campaign with the offending seed
//! regenerates the exact same case.
//!
//! It is a thin wrapper over a SplitMix64 / xorshift core rather than `rand`'s `StdRng` so
//! that the byte stream is stable across `rand` version bumps (a reproducer recorded today
//! must still reproduce after a dependency upgrade).

/// A small, fast, fully deterministic PRNG (SplitMix64).
#[derive(Debug, Clone)]
pub struct Rng {
    state: u64,
}

impl Rng {
    #[must_use]
    pub const fn new(seed: u64) -> Self {
        // Avoid the all-zero state degenerating; SplitMix64 handles 0 fine but we mix anyway.
        Self {
            state: seed ^ 0x9E37_79B9_7F4A_7C15,
        }
    }

    /// Next raw 64-bit word.
    pub fn next_u64(&mut self) -> u64 {
        // SplitMix64
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform `u32`.
    pub fn next_u32(&mut self) -> u32 {
        (self.next_u64() >> 32) as u32
    }

    /// Uniform in `[0, n)`. Returns 0 if `n == 0`.
    pub fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            return 0;
        }
        // Lemire-ish: good enough, fully deterministic.
        (self.next_u64() % (n as u64)) as usize
    }

    /// Inclusive range `[lo, hi]`.
    pub fn range(&mut self, lo: usize, hi: usize) -> usize {
        debug_assert!(lo <= hi);
        lo + self.below(hi - lo + 1)
    }

    /// `true` with probability `num/den`.
    pub fn chance(&mut self, num: u32, den: u32) -> bool {
        debug_assert!(den > 0);
        self.next_u32() % den < num
    }

    /// Fair coin.
    pub fn flip(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }

    /// Pick a reference to a random element of a non-empty slice.
    pub fn choice<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        debug_assert!(!items.is_empty());
        &items[self.below(items.len())]
    }

    /// Pick a random index of a non-empty slice.
    pub fn choose_index(&mut self, len: usize) -> usize {
        debug_assert!(len > 0);
        self.below(len)
    }

    /// Fisher–Yates shuffle.
    pub fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() {
            let j = self.below(i + 1);
            items.swap(i, j);
        }
    }
}
