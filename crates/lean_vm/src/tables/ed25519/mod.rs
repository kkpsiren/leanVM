//! ed25519 batch-validity tables (docs/zk-aggregate-spec.md in farcaster-blobs): shared gadgets,
//! the native curve, and the VM tables (EdSig, DecompressA, …).
pub mod curve;
pub mod decompress_table;
pub mod edsig_table;
pub mod gadgets;
pub mod ed_add_table;
pub mod scalar_table;
pub mod sha512_table;
pub mod signer_scalar_table;
pub use decompress_table::{ED_DECOMPRESS_NAME, EdDecompressTable};
pub use edsig_table::{ED_SIG_NAME, EdSigTable};
pub use ed_add_table::{EdAddTable, fill_trace_ed_add};
pub use scalar_table::{SCALAR_L_NAME, ScalarLTable};
pub use sha512_table::{SHA512_NAME, Sha512Table};
pub use signer_scalar_table::{SIGNER_SCALAR_NAME, SignerScalarTable};

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
        // Phase B tables: sectioned range classes; report the uncovered ranges (must be bits, flags, bus/pointer, linear-in-bits or chain-bounded columns)
        for (name, n_cols, classes) in [
            ("sha512", super::sha512_table::N_COLS, super::sha512_table::range_cols()),
            ("scalar_l", super::scalar_table::N_COLS, super::scalar_table::range_cols()),
            ("signer_scalar", super::signer_scalar_table::N_COLS, super::signer_scalar_table::range_cols()),
        ] {
            let mut all: Vec<usize> = classes.iter().flat_map(|(_, c)| c.iter().copied()).collect();
            let n = all.len(); all.sort_unstable(); all.dedup();
            assert_eq!(all.len(), n, "{name}: duplicate range column");
            assert!(*all.last().unwrap() < n_cols, "{name}: range column out of layout");
            let mut ranges: Vec<(usize, usize)> = vec![];
            for c in (0..n_cols).filter(|c| all.binary_search(c).is_err()) { match ranges.last_mut() { Some((_, e)) if *e + 1 == c => *e = c, _ => ranges.push((c, c)) } }
            println!("{name}: pushes={} covered={}/{} uncovered ranges={:?}", n, n, n_cols, ranges);
        }
    }
}

#[cfg(test)]
mod constraint_counts {
    use crate::*;
    use backend::*;
    struct Counter { flat: Vec<F>, shift: Vec<F>, n: usize }
    impl AirBuilder for Counter {
        type F = F; type IF = F; type EF = EF;
        fn flat(&self) -> &[F] { &self.flat }
        fn shift(&self) -> &[F] { &self.shift }
        fn assert_zero(&mut self, _x: F) { self.n += 1; }
        fn assert_zero_ef(&mut self, _x: EF) { self.n += 1; }
    }
    fn count<A: Air<ExtraData = ExtraDataForBuses<EF>>>(air: &A) -> usize {
        let mut b = Counter { flat: vec![F::ZERO; air.n_columns()], shift: vec![F::ZERO; air.n_columns()], n: 0 };
        air.eval(&mut b, &ExtraDataForBuses::new(&[], vec![]));
        b.n
    }
    /// The declared `n_constraints` must equal the emitted constraints plus 2 alpha slots per Column bus.
    #[test]
    fn declared_constraint_counts_match() {
        let cases: Vec<(&str, usize, usize, usize)> = vec![
            ("ed_sig", count(&super::EdSigTable::<false>), n_column_buses(&Table::ed_sig().bus_interactions()), Table::ed_sig().n_constraints()),
            ("ed_decompress", count(&super::EdDecompressTable::<false>), n_column_buses(&Table::ed_decompress().bus_interactions()), Table::ed_decompress().n_constraints()),
            ("sha512", count(&super::Sha512Table::<false>), n_column_buses(&Table::sha512().bus_interactions()), Table::sha512().n_constraints()),
            ("scalar_l", count(&super::ScalarLTable::<false>), n_column_buses(&Table::scalar_l().bus_interactions()), Table::scalar_l().n_constraints()),
            ("signer_scalar", count(&super::SignerScalarTable::<false>), n_column_buses(&Table::signer_scalar().bus_interactions()), Table::signer_scalar().n_constraints()),
            ("ed_add", count(&super::EdAddTable::<false>), n_column_buses(&Table::ed_add().bus_interactions()), Table::ed_add().n_constraints()),
        ];
        let mut bad = vec![];
        for (name, emitted, buses, declared) in &cases {
            println!("{name}: emitted {emitted} + 2·{buses} buses = {} vs declared {declared}", emitted + 2 * buses);
            if emitted + 2 * buses != *declared { bad.push(*name); }
        }
        assert!(bad.is_empty(), "declared n_constraints wrong for {bad:?}");
    }
}
