//! Canonical single-blob tree, independent of proof transcripts and recursion bytecode.
//!
//! Group consecutive children by four at every level, including a short (even unary) last group.
//! Never promote a leftover child. Always wrap the final level in a published top node.
use backend::Evaluation;
use lean_prover::ed25519_leaf::{ED25519_SCHEME_ID, MAX_LEAF_SIGS, SigRow};
use lean_vm::{EF, F};

use crate::ed25519::{NODE_FAN_IN, NodeShape, Statement};

pub const MAX_BLOB_TREE_DEPTH: usize = 16;

#[derive(Debug, Clone)]
pub struct BlobTreeLayout {
    pub scheme_id: u32,
    pub n_rows: usize,
    pub leaf_size: usize,
    // Width of each level below the published top, starting with the leaves.
    widths: Vec<usize>,
}

impl BlobTreeLayout {
    pub fn new(n_rows: usize, leaf_size: usize) -> Result<Self, String> {
        Self::for_scheme(ED25519_SCHEME_ID, n_rows, leaf_size)
    }

    pub fn for_scheme(scheme_id: u32, n_rows: usize, leaf_size: usize) -> Result<Self, String> {
        if scheme_id != ED25519_SCHEME_ID {
            return Err(format!("unsupported leaf scheme {scheme_id}"));
        }
        if n_rows == 0 || n_rows > u32::MAX as usize {
            return Err("row count must be 1..=u32::MAX".into());
        }
        if leaf_size == 0 || leaf_size > MAX_LEAF_SIGS {
            return Err(format!("leaf size must be 1..={MAX_LEAF_SIGS}"));
        }
        let n_leaves = n_rows.div_ceil(leaf_size);
        if n_leaves > 1 << 30 {
            return Err("leaf indices must be below 2^30".into());
        }
        let mut widths = vec![n_leaves];
        while *widths.last().unwrap() > NODE_FAN_IN {
            widths.push(widths.last().unwrap().div_ceil(NODE_FAN_IN));
        }
        if widths.len() > MAX_BLOB_TREE_DEPTH {
            return Err("tree is too deep".into());
        }
        Ok(Self {
            scheme_id,
            n_rows,
            leaf_size,
            widths,
        })
    }

    pub fn level_widths(&self) -> &[usize] {
        &self.widths
    }
    pub fn n_leaves(&self) -> usize {
        self.widths[0]
    }
    pub fn n_inner_nodes(&self) -> usize {
        self.widths[1..].iter().sum()
    }

    /// Inner claims are in depth-first pre-order, excluding the published top and all leaves.
    /// Check the count BEFORE constructing any tree, including for hostile huge row counts.
    pub fn shape(&self, claims: &[Evaluation<EF>]) -> Result<Vec<NodeShape>, String> {
        if claims.len() != self.n_inner_nodes() {
            return Err("wrong inner claim count".into());
        }
        fn build(
            layout: &BlobTreeLayout,
            level: usize,
            i: usize,
            claims: &mut std::slice::Iter<'_, Evaluation<EF>>,
        ) -> NodeShape {
            if level == 0 {
                return NodeShape::Leaf;
            }
            let claim = claims.next().unwrap().clone();
            let children = (i * NODE_FAN_IN..((i + 1) * NODE_FAN_IN).min(layout.widths[level - 1]))
                .map(|j| build(layout, level - 1, j, claims))
                .collect();
            NodeShape::Node { claim, children }
        }
        let level = self.widths.len() - 1;
        let mut claims = claims.iter();
        Ok((0..self.widths[level])
            .map(|i| build(self, level, i, &mut claims))
            .collect())
    }

    /// Validate exact grouping, then extract claims in the wire order. A tree with the right leaf
    /// count but different grouping (including unary promotions or a mixed level) is rejected.
    pub fn claims(&self, shape: &[NodeShape]) -> Result<Vec<Evaluation<EF>>, String> {
        fn visit(
            layout: &BlobTreeLayout,
            level: usize,
            i: usize,
            shape: &NodeShape,
            out: &mut Vec<Evaluation<EF>>,
        ) -> Result<(), String> {
            match (level, shape) {
                (0, NodeShape::Leaf) => Ok(()),
                (0, _) | (_, NodeShape::Leaf) => Err("noncanonical tree level".into()),
                (_, NodeShape::Node { claim, children }) => {
                    let start = i * NODE_FAN_IN;
                    let end = ((i + 1) * NODE_FAN_IN).min(layout.widths[level - 1]);
                    if children.len() != end - start {
                        return Err("noncanonical child count".into());
                    }
                    out.push(claim.clone());
                    for (j, child) in (start..end).zip(children) {
                        visit(layout, level - 1, j, child, out)?;
                    }
                    Ok(())
                }
            }
        }
        let level = self.widths.len() - 1;
        if shape.len() != self.widths[level] {
            return Err("noncanonical top child count".into());
        }
        let mut claims = Vec::new();
        for (i, child) in shape.iter().enumerate() {
            visit(self, level, i, child, &mut claims)?;
        }
        Ok(claims)
    }

    /// The statement is derived solely from the reader's rows, segmentation and blob identifier.
    pub fn statements<'a>(&self, rows: &'a [SigRow], blob_id: &[F; 9]) -> Result<Vec<Statement<'a>>, String> {
        if self.scheme_id != ED25519_SCHEME_ID {
            return Err("unsupported leaf scheme".into());
        }
        if rows.len() != self.n_rows {
            return Err("row count differs from layout".into());
        }
        fn build<'a>(
            layout: &BlobTreeLayout,
            level: usize,
            i: usize,
            rows: &'a [SigRow],
            blob_id: &[F; 9],
        ) -> Statement<'a> {
            if level == 0 {
                let start = i * layout.leaf_size;
                return Statement::Leaf {
                    scheme_id: layout.scheme_id,
                    rows: &rows[start..(start + layout.leaf_size).min(rows.len())],
                    seg_index: i,
                    blob_id: *blob_id,
                };
            }
            Statement::Node(
                (i * NODE_FAN_IN..((i + 1) * NODE_FAN_IN).min(layout.widths[level - 1]))
                    .map(|j| build(layout, level - 1, j, rows, blob_id))
                    .collect(),
            )
        }
        let level = self.widths.len() - 1;
        Ok((0..self.widths[level])
            .map(|i| build(self, level, i, rows, blob_id))
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::*;

    #[test]
    fn leaf_scheme_is_explicit_and_unknown_schemes_fail_before_vk_initialization() {
        use crate::ed25519::expected_digest;
        use lean_prover::ed25519_leaf::leaf_meta;
        assert!(BlobTreeLayout::for_scheme(1, 1, 1).is_err());
        let rows = [SigRow {
            pubkey: [0; 32],
            digest: [0; 20],
            sig: [0; 64],
        }];
        let layout = BlobTreeLayout::for_scheme(ED25519_SCHEME_ID, 1, 1).unwrap();
        let stmts = layout.statements(&rows, &[F::ZERO; 9]).unwrap();
        assert!(matches!(
            stmts[0],
            Statement::Leaf {
                scheme_id: ED25519_SCHEME_ID,
                ..
            }
        ));
        let unknown = Statement::Leaf {
            scheme_id: 1,
            rows: &rows,
            seg_index: 0,
            blob_id: [F::ZERO; 9],
        };
        assert!(expected_digest(&unknown, &NodeShape::Leaf).is_err());
        let meta = leaf_meta(1, 0, &[F::ZERO; 9]);
        assert_eq!(meta[3], F::ZERO); // Existing preimage unchanged; zero now explicitly names the scheme.
    }

    #[test]
    fn canonical_boundaries_and_claim_order() {
        for (leaves, widths) in [
            (1, vec![1]),
            (4, vec![4]),
            (5, vec![5, 2]),
            (16, vec![16, 4]),
            (17, vec![17, 5, 2]),
            (49, vec![49, 13, 4]),
            (65, vec![65, 17, 5, 2]),
        ] {
            let layout = BlobTreeLayout::new(leaves * 16 - 3, 16).unwrap();
            assert_eq!(layout.level_widths(), widths);
            let claims: Vec<_> = (0..layout.n_inner_nodes())
                .map(|i| Evaluation::new(MultilinearPoint(vec![EF::from_usize(i)]), EF::from_usize(i + 100)))
                .collect();
            let shape = layout.shape(&claims).unwrap();
            let recovered = layout.claims(&shape).unwrap();
            assert_eq!(
                recovered.iter().map(|c| c.value).collect::<Vec<_>>(),
                claims.iter().map(|c| c.value).collect::<Vec<_>>()
            );
            assert!(
                layout
                    .shape(
                        &[
                            claims.clone(),
                            vec![Evaluation::new(MultilinearPoint(vec![]), EF::ZERO)]
                        ]
                        .concat()
                    )
                    .is_err()
            );
            let rows = vec![
                SigRow {
                    pubkey: [0; 32],
                    digest: [0; 20],
                    sig: [0; 64]
                };
                layout.n_rows
            ];
            fn visit(stmts: &[Statement<'_>], next: &mut usize, rows_seen: &mut usize) {
                for stmt in stmts {
                    match stmt {
                        Statement::Leaf { rows, seg_index, .. } => {
                            assert_eq!(*seg_index, *next);
                            *next += 1;
                            *rows_seen += rows.len();
                        }
                        Statement::Node(children) => visit(children, next, rows_seen),
                    }
                }
            }
            let (mut next, mut seen) = (0, 0);
            visit(&layout.statements(&rows, &[F::ZERO; 9]).unwrap(), &mut next, &mut seen);
            assert_eq!((next, seen), (leaves, rows.len()));
        }
    }

    #[test]
    fn rejects_noncanonical_shapes_and_invalid_parameters() {
        for (n, s) in [(0, 16), (1, 0), (1, MAX_LEAF_SIGS + 1), ((1 << 30) + 1, 1)] {
            assert!(BlobTreeLayout::new(n, s).is_err());
        }
        let layout = BlobTreeLayout::new(65, 16).unwrap();
        let claim = Evaluation::new(MultilinearPoint(vec![]), EF::ZERO);
        let mut shape = layout.shape(&[claim.clone(), claim]).unwrap();
        assert!(layout.shape(&[]).is_err());
        // Five leaves must be (four, one), not (one, four), (three, two), or a promoted leaf.
        shape.swap(0, 1);
        assert!(layout.claims(&shape).is_err());
        shape.swap(0, 1);
        if let NodeShape::Node { children, .. } = &mut shape[0] {
            children.pop();
        }
        if let NodeShape::Node { children, .. } = &mut shape[1] {
            children.push(NodeShape::Leaf);
        }
        assert!(layout.claims(&shape).is_err());
        shape[1] = NodeShape::Leaf;
        assert!(layout.claims(&shape).is_err());
        assert!(BlobTreeLayout::new(1 << 30, 1).unwrap().shape(&[]).is_err());
    }
}
