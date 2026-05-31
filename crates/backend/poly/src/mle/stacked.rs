use crate::*;
use field::{ExtensionField, PackedValue, PrimeCharacteristicRing};
use rayon::prelude::*;

/// One segment of a [`StackedPoly`]: a contiguous run of `data.len() >> log_block`
/// power-of-two MLE blocks, each of size `2^log_block`, starting at global index
/// `offset`. `offset` is a multiple of `2^log_block` (so each sub-block is aligned).
///
/// Tables are a single segment whose `data` is the committed column-major prefix
/// (`log_block` = the table height): `data.len() = n_columns << log_block`.
#[derive(Debug, Clone, Copy)]
pub struct StackedSegment<'a, EF: ExtensionField<PF<EF>>> {
    pub offset: usize,
    pub data: &'a [PF<EF>],
    pub log_block: usize,
}

/// A view over the logical concatenation of several base-field segments (plus implicit
/// zeros in the gaps and trailing padding), seen as one multilinear polynomial over
/// `n_vars` variables. Lets WHIR commit/prove the stacked polynomial without ever
/// materializing it.
#[derive(Debug)]
pub struct StackedPoly<'a, EF: ExtensionField<PF<EF>>> {
    pub n_vars: usize,
    /// Highest index holding data (= end of the last segment). Indices `[active_len, 2^n_vars)` are zero.
    pub active_len: usize,
    /// Segments sorted by ascending `offset`, pairwise disjoint.
    pub segments: Vec<StackedSegment<'a, EF>>,
}

/// A maximal range `[start, start+len)` (in packed units) over which, for each of the `K`
/// query offsets, the source stays within a single segment (or entirely in a zero gap).
#[derive(Debug)]
pub struct StackedRun<'a, EF: ExtensionField<PF<EF>>, const K: usize> {
    pub start: usize,
    pub len: usize,
    /// For query offset `j`, the packed source slice of length `len`, or `None` for zeros.
    pub srcs: [Option<&'a [PFPacking<EF>]>; K],
}

impl<'a, EF: ExtensionField<PF<EF>>> StackedPoly<'a, EF> {
    pub fn new(n_vars: usize, mut segments: Vec<StackedSegment<'a, EF>>) -> Self {
        segments.sort_by_key(|s| s.offset);
        let mut active_len = 0;
        for s in &segments {
            let block = 1usize << s.log_block;
            assert_eq!(s.offset % block, 0, "segment offset not block-aligned");
            assert_eq!(s.data.len() % block, 0, "segment length not block-aligned");
            assert!(s.offset >= active_len, "segments overlap or are unsorted");
            active_len = s.offset + s.data.len();
        }
        assert!(active_len <= (1 << n_vars));
        Self {
            n_vars,
            active_len,
            segments,
        }
    }

    /// Value of the stacked polynomial at index `i` (zero outside the segments).
    #[inline]
    pub fn value_at(&self, i: usize) -> PF<EF> {
        for s in &self.segments {
            if i < s.offset {
                break; // gap: sorted segments, so no later one covers i either
            }
            if i < s.offset + s.data.len() {
                return s.data[i - s.offset];
            }
        }
        PF::<EF>::ZERO
    }

    /// Multilinear evaluation at `point`, computed block-by-block (no materialization):
    /// `eval = Σ_blocks eq(block_high_index, point_high) * block.evaluate(point_low)`.
    pub fn evaluate(&self, point: &MultilinearPoint<EF>) -> EF {
        assert_eq!(point.len(), self.n_vars);
        self.segments
            .par_iter()
            .map(|s| {
                let b = s.log_block;
                let hi_vars = self.n_vars - b;
                let point_hi = MultilinearPoint(point.0[..hi_vars].to_vec());
                let point_lo = MultilinearPoint(point.0[hi_vars..].to_vec());
                let n_blocks = s.data.len() >> b;
                (0..n_blocks)
                    .into_par_iter()
                    .map(|blk| {
                        let block_index = (s.offset >> b) + blk;
                        let eq =
                            MultilinearPoint(to_big_endian_in_field(block_index, hi_vars)).eq_poly_outside(&point_hi);
                        let block = &s.data[blk << b..][..1 << b];
                        eq * block.evaluate(&point_lo)
                    })
                    .sum::<EF>()
            })
            .sum()
    }

    /// The segments as packed base slices, with packed offsets. Requires every segment
    /// offset and length to be a multiple of the packing width (guaranteed: blocks are >= 2^8).
    fn packed_segments(&self) -> Vec<(usize, &'a [PFPacking<EF>])> {
        let w = packing_width::<EF>();
        self.segments
            .iter()
            .map(|s| {
                debug_assert_eq!(s.offset % w, 0);
                debug_assert_eq!(s.data.len() % w, 0);
                (s.offset / w, PFPacking::<EF>::pack_slice(s.data))
            })
            .collect()
    }

    /// Partition `[0, count)` (packed units) into runs where, for every query offset in
    /// `offsets`, the source `offsets[j] + p` stays inside a single segment (or a gap).
    pub fn runs<const K: usize>(&self, offsets: [usize; K], count: usize) -> Vec<StackedRun<'a, EF, K>> {
        let segs = self.packed_segments();

        // Boundaries: positions in [0, count] where any queried source crosses a segment edge.
        let mut bps = vec![0usize, count];
        for &(off, slice) in &segs {
            for edge in [off, off + slice.len()] {
                for &q in &offsets {
                    if edge >= q {
                        let p = edge - q;
                        if p <= count {
                            bps.push(p);
                        }
                    }
                }
            }
        }
        bps.sort_unstable();
        bps.dedup();

        bps.windows(2)
            .map(|w| {
                let (a, len) = (w[0], w[1] - w[0]);
                let srcs = std::array::from_fn(|j| {
                    let pos = offsets[j] + a;
                    segs.iter().find_map(|&(off, slice)| {
                        (pos >= off && pos + len <= off + slice.len()).then(|| &slice[pos - off..pos - off + len])
                    })
                });
                StackedRun { start: a, len, srcs }
            })
            .collect()
    }

    /// Fold the stacked polynomial by `r` along the highest variable (pairs `i` with `i + 2^(n-1)`),
    /// returning the (owned, contiguous) folded evaluations. Only used when the initial WHIR
    /// folding factor is 1 (not the case for the production config).
    pub fn fold_to_owned(&self, r: EF) -> Vec<EF> {
        let half = 1 << (self.n_vars - 1);
        (0..half)
            .into_par_iter()
            .map(|k| {
                let lo = self.value_at(k);
                let hi = self.value_at(half + k);
                EF::from(lo) + r * (hi - lo)
            })
            .collect()
    }
}
