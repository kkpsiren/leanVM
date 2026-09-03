//! ed25519 batch-validity tables (docs/zk-aggregate-spec.md in farcaster-blobs): shared gadgets,
//! the native curve, and the VM tables (EdSig, DecompressA, …).
pub mod curve;
pub mod decompress_table;
pub mod edsig_table;
pub mod gadgets;
pub use decompress_table::{ED_DECOMPRESS_NAME, EdDecompressTable};
pub use edsig_table::{ED_SIG_NAME, EdSigTable};

#[cfg(test)]
mod range_coverage {
    #[test]
    fn range_cols_distinct_and_report() {
        for (name, n_cols, (u8s, u16s, u7s)) in [
            ("ed_sig", super::edsig_table::N_COLS, super::edsig_table::range_cols()),
            ("ed_decompress", super::decompress_table::N_COLS, super::decompress_table::range_cols()),
        ] {
            let mut all: Vec<usize> = u8s.iter().chain(&u16s).chain(&u7s).copied().collect();
            let n = all.len();
            all.sort_unstable(); all.dedup();
            assert_eq!(all.len(), n, "{name}: duplicate range column");
            assert!(*all.last().unwrap() < n_cols, "{name}: range column out of layout");
            let uncovered: Vec<usize> = (0..n_cols).filter(|c| all.binary_search(c).is_err()).collect();
            println!("{name}: u8={} u16={} u7={} covered={}/{} uncovered={:?}", u8s.len(), u16s.len(), u7s.len(), n, n_cols, uncovered);
        }
    }
}
