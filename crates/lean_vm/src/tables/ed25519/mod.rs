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

#[cfg(test)]
mod routing_soundness {
    use crate::*;
    use backend::*;
    struct Fail { flat: Vec<F>, n: usize, failures: usize }
    impl AirBuilder for Fail {
        type F = F; type IF = F; type EF = EF;
        fn flat(&self) -> &[F] { &self.flat }
        fn shift(&self) -> &[F] { &[] }
        fn assert_zero(&mut self, x: F) { if x != F::ZERO { self.failures += 1; } self.n += 1; }
        fn assert_zero_ef(&mut self, x: EF) { if x != EF::ZERO { self.failures += 1; } self.n += 1; }
    }
    fn run<A: Air<ExtraData = ExtraDataForBuses<EF>>>(air: &A, row: &[F]) -> usize {
        let mut b = Fail { flat: row.to_vec(), n: 0, failures: 0 };
        air.eval(&mut b, &ExtraDataForBuses::new(&[], vec![])); b.failures
    }
    /// A row that routes (some nz=1) but is marked inactive (mult=0) must be rejected: otherwise a
    /// padding row injects an arbitrary (scalar, point) into the MSM (codex finding #2, universal forgery).
    #[test]
    fn inactive_rows_cannot_route() {
        use super::{scalar_table as t4, signer_scalar_table as t7};
        // ScalarL: a valid active row with a nonzero rho (⇒ some nz=1)
        let mut row = t4::make_row(&[0u8; 64], &[0u8; 32], &[12345, 0, 0, 0], &[0u64; 32], &[0u64; 32], 0, 0, 0, 0);
        assert_eq!(run(&t4::ScalarLTable::<false>, &row), 0, "the honest active ScalarL row must satisfy every constraint");
        assert!((0..t4::WINDOWS).any(|j| row[t4::COL_NZ + j] == F::ONE), "test needs at least one routed window");
        row[t4::COL_MULT] = F::ZERO; // mark inactive but leave the routes
        assert!(run(&t4::ScalarLTable::<false>, &row) > 0, "an inactive ScalarL row that still routes must be rejected");
        // SignerScalar: a valid active row with nonzero K (⇒ some nz=1)
        let mut k = [0i64; 32]; k[0] = 7; k[1] = 99;
        let mut row = t7::make_row(&k, 0, false, 0, 0);
        assert_eq!(run(&t7::SignerScalarTable::<false>, &row), 0, "the honest active SignerScalar row must satisfy every constraint");
        assert!((0..t7::T7_WINDOWS).any(|j| row[t7::COL_NZ + j] == F::ONE), "test needs at least one routed window");
        row[t7::COL_MULT] = F::ZERO;
        assert!(run(&t7::SignerScalarTable::<false>, &row) > 0, "an inactive SignerScalar row that still routes must be rejected");
    }
}

#[cfg(test)]
mod g8_range_coverage {
    //! The G8 soundness argument (gadgets.rs) needs every `q` limb checked to ≤ 8 bits and every `w`
    //! limb to ≤ 16 bits. The layouts are hand-written per table, so this test derives the limb
    //! columns from the symbolic identities and asserts they are registered range columns.
    use crate::F;
    use crate::tables::table_trait::RANGE_SECTIONS;
    use backend::{SymbolicExpression, get_symbolic_constraints_and_bus_data_values};
    use std::collections::BTreeSet;

    fn col_of(e: &SymbolicExpression<F>, n_cols: usize) -> usize {
        match e { SymbolicExpression::Variable(v) => v.index % n_cols, _ => panic!("G8 limb operand is not a plain column") }
    }
    fn from_tuple((u8s, u16s, u7s): (Vec<usize>, Vec<usize>, Vec<usize>)) -> (BTreeSet<usize>, BTreeSet<usize>) {
        let small: BTreeSet<usize> = u8s.iter().chain(&u7s).copied().collect();
        let wide: BTreeSet<usize> = small.iter().chain(&u16s).copied().collect();
        (small, wide)
    }
    fn from_sections(classes: Vec<(usize, Vec<usize>)>) -> (BTreeSet<usize>, BTreeSet<usize>) {
        let mut small = BTreeSet::new(); let mut wide = BTreeSet::new();
        for (sec, cols) in classes { let bits = RANGE_SECTIONS[sec].bits; for c in cols { if bits <= 8 { small.insert(c); } if bits <= 16 { wide.insert(c); } } }
        (small, wide)
    }
    fn check<A: backend::Air>(name: &str, air: &A, n_cols: usize, (small, wide): (BTreeSet<usize>, BTreeSet<usize>))
    where A::ExtraData: Default {
        let (_, _, identities) = get_symbolic_constraints_and_bus_data_values::<F, _>(air);
        assert!(!identities.is_empty(), "{name}: expected G8 identities");
        for (k, id) in identities.iter().enumerate() {
            for e in &id.q { let c = col_of(e, n_cols); assert!(small.contains(&c), "{name}: identity {k}: q limb column {c} is not range-checked to ≤ 8 bits"); }
            for e in &id.w { let c = col_of(e, n_cols); assert!(wide.contains(&c), "{name}: identity {k}: w limb column {c} is not range-checked to ≤ 16 bits"); }
            // the integer-lift argument also needs byte-bounded result limbs and product operands
            if let Some(r) = &id.r { for e in r { let c = col_of(e, n_cols); assert!(small.contains(&c), "{name}: identity {k}: r limb column {c} is not range-checked to ≤ 8 bits"); } }
            for (a, b, _) in &id.products {
                for e in a.iter().chain(b) { if let SymbolicExpression::Variable(v) = e { let c = v.index % n_cols; assert!(small.contains(&c), "{name}: identity {k}: product operand column {c} is not range-checked to ≤ 8 bits"); } }
            }
        }
        println!("{name}: {} identities, all q/w limbs range-checked", identities.len());
    }
    #[test]
    fn g8_identity_limbs_are_range_checked() {
        check("ed_sig", &super::edsig_table::EdSigTable::<false>, super::edsig_table::N_COLS, from_tuple(super::edsig_table::range_cols()));
        check("ed_decompress", &super::decompress_table::EdDecompressTable::<false>, super::decompress_table::N_COLS, from_tuple(super::decompress_table::range_cols()));
        check("scalar_l", &super::scalar_table::ScalarLTable::<false>, super::scalar_table::N_COLS, from_sections(super::scalar_table::range_cols()));
        {
            // SignerScalar bounds its reduced-scalar limbs (the identity's r) by bit decomposition, not by a
            // range push: kred[i] = Σ_t bits[8i+t]·2^t with every bit asserted boolean, which is a tighter
            // bound than U8. Accept those columns as byte-bounded.
            use super::signer_scalar_table as t7;
            let (mut small, wide) = from_sections(t7::range_cols());
            small.extend(t7::COL_KRED..t7::COL_KRED + 32);
            check("signer_scalar", &t7::SignerScalarTable::<false>, t7::N_COLS, (small, wide));
        }
        {
            // EdAdd reads point coordinates (px, py) from memory records written by EdSig / Decompress,
            // whose output limbs are U8-checked in those tables (verified above); the memory lookup pins
            // equality, so those columns are byte-bounded by provenance rather than by a local range push.
            use super::ed_add_table as t3;
            use crate::tables::table_trait::TableT;
            let (mut small, wide) = from_sections(t3::range_cols());
            for b in t3::EdAddTable::<false>.bus_interactions() {
                if b.is_memory_lookup() { for d in &b.data { if let Some(c) = d.column() { small.insert(c); } } }
            }
            // and the selected coordinates px/py are gated copies of those memory columns (a boolean
            // times a byte, or the neutral point's constants), so they carry the same bound
            small.extend(t3::COL_PX..t3::COL_PX + 64);
            check("ed_add", &t3::EdAddTable::<false>, t3::N_COLS, (small, wide));
        }
    }
}

#[cfg(test)]
mod domainseps {
    //! LogUp domain separators: a collision between two unrelated buses would let them balance against
    //! each other silently. Convention: table buses are ≡ 2 (mod 4), ≥ 6 (memory = 1, bytecode = 2);
    //! range-section alive/dead domainseps are reserved for the range region and never appear on a
    //! non-range table bus.
    use crate::tables::table_trait::{BusData, RANGE_SECTIONS, TableT};
    use crate::{ALL_TABLES, LOGUP_BYTECODE_DOMAINSEP, LOGUP_MEMORY_DOMAINSEP, Table};
    use std::collections::BTreeSet;
    #[test]
    fn logup_domainseps_do_not_collide() {
        let range_ds: BTreeSet<usize> = RANGE_SECTIONS.iter().flat_map(|s| [s.domainsep, s.dead_domainsep]).collect();
        assert_eq!(range_ds.len(), 2 * RANGE_SECTIONS.len(), "range section domainseps collide");
        let mut seen = BTreeSet::new();
        let mut widths: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
        for t in ALL_TABLES {
            for b in t.bus_interactions() {
                let BusData::Constant(ds) = b.domainsep else {
                    // column-typed domainseps: only the three stock tables use them, and their formulas
                    // (exec: an instruction column; poseidon: 3 + 2·f + 4·f + 8·f + 16·f·offset, odd;
                    // extension_op: 4·f + 8·f + 16·f + 32·f + 64·len, ≡ 0 mod 4) never land in the 2-mod-4 class
                    assert!(t == Table::execution() || t == Table::poseidon16() || t == Table::extension_op(), "{t:?}: a column-typed domainsep on a table whose formula is not checked here");
                    continue;
                };
                if b.range_section().is_some() { assert!(RANGE_SECTIONS.iter().any(|s| s.domainsep == ds), "range push with a non-alive domainsep {ds}"); continue; }
                assert!(ds == LOGUP_MEMORY_DOMAINSEP || ds == LOGUP_BYTECODE_DOMAINSEP || (ds % 4 == 2 && ds >= 6), "{t:?}: bus domainsep {ds} breaks the 2-mod-4 convention");
                assert!(!range_ds.contains(&ds), "{t:?}: bus domainsep {ds} collides with a range section");
                // one domainsep = one bus: every push and pull on it must carry the same data width
                let w = b.data.len();
                if let Some(prev) = widths.insert(ds, w) { assert_eq!(prev, w, "{t:?}: domainsep {ds} is used with data widths {prev} and {w} (two different buses share it)"); }
                seen.insert(ds);
            }
        }
        println!("table bus domainseps: {seen:?}; range: {range_ds:?}");
    }
}
