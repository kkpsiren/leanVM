// Credits:
// - whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).
// - Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::any::TypeId;

use field::BasedVectorSpace;
use field::ExtensionField;
use field::Field;
use field::PackedValue;
use field::PrimeCharacteristicRing;
use goldilocks::{CubicExtensionFieldGL, Goldilocks, default_goldilocks_poseidon1_8};
use poly::*;

use symetric::merkle::unpack_array;
use tracing::instrument;
use utils::log2_ceil_usize;
use zk_alloc::ArenaVec;

use crate::Dimensions;
use crate::Matrix;
use crate::utils::flatten_to_base_arena;
pub use symetric::DIGEST_ELEMS;

pub(crate) type RoundMerkleTree<F> = WhirMerkleTree<F, DIGEST_ELEMS>;

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_commit<F: Field, EF: ExtensionField<F>>(
    matrix: Matrix<EF, ArenaVec<EF>>,
    full_n_cols: usize,
    effective_n_cols: usize,
) -> ([F; DIGEST_ELEMS], RoundMerkleTree<F>) {
    if TypeId::of::<(F, EF)>() == TypeId::of::<(Goldilocks, CubicExtensionFieldGL)>() {
        let matrix =
            unsafe { std::mem::transmute::<_, Matrix<CubicExtensionFieldGL, ArenaVec<CubicExtensionFieldGL>>>(matrix) };
        let dim = <CubicExtensionFieldGL as BasedVectorSpace<Goldilocks>>::DIMENSION;
        let dft_base_width = matrix.width * dim;
        let full_base_width = full_n_cols * dim;
        let effective_base_width = effective_n_cols * dim;
        let base_values = flatten_to_base_arena::<Goldilocks, CubicExtensionFieldGL>(matrix.values);
        let base_matrix = Matrix::new(base_values, dft_base_width);
        let tree = build_merkle_tree_goldilocks(base_matrix, full_base_width, effective_base_width);
        let root: [_; DIGEST_ELEMS] = tree.root();
        let root = unsafe { std::mem::transmute_copy::<_, [F; DIGEST_ELEMS]>(&root) };
        let tree = unsafe { std::mem::transmute::<_, RoundMerkleTree<F>>(tree) };
        (root, tree)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(Goldilocks, Goldilocks)>() {
        let matrix = unsafe { std::mem::transmute::<_, Matrix<Goldilocks, ArenaVec<Goldilocks>>>(matrix) };
        let tree = build_merkle_tree_goldilocks(matrix, full_n_cols, effective_n_cols);
        let root: [_; DIGEST_ELEMS] = tree.root();
        let root = unsafe { std::mem::transmute_copy::<_, [F; DIGEST_ELEMS]>(&root) };
        let tree = unsafe { std::mem::transmute::<_, RoundMerkleTree<F>>(tree) };
        (root, tree)
    } else {
        unimplemented!()
    }
}

#[instrument(name = "build merkle tree", skip_all)]
fn build_merkle_tree_goldilocks(
    leaf: Matrix<Goldilocks, ArenaVec<Goldilocks>>,
    full_base_width: usize,
    effective_base_width: usize,
) -> RoundMerkleTree<Goldilocks> {
    // Leaf hashing is an overwrite sponge (raw permutation); the 2->1 tree climb is compression.
    // `perm` (Poseidon8) implements both `Permutation` and `Compression`, so it serves both roles.
    let perm = default_goldilocks_poseidon1_8();
    let n_zero_suffix_rate_chunks = (full_base_width - effective_base_width) / 4;
    let iv_first = Goldilocks::from_usize(full_base_width);
    let scalar_state = symetric::precompute_zero_suffix_state::<Goldilocks, _, 8, 4, DIGEST_ELEMS>(
        &perm,
        iv_first,
        n_zero_suffix_rate_chunks,
    );
    let packed_state: [PFPacking<Goldilocks>; 8] =
        std::array::from_fn(|i| PFPacking::<Goldilocks>::from_fn(|_| scalar_state[i]));
    let first_layer = first_digest_layer_with_initial_state::<PFPacking<Goldilocks>, _, _, DIGEST_ELEMS, 8, 4>(
        &perm,
        &leaf,
        &packed_state,
        effective_base_width,
    );
    let tree = symetric::merkle::MerkleTree::from_first_layer::<PFPacking<Goldilocks>, _, 8>(&perm, first_layer);
    WhirMerkleTree {
        leaf,
        tree,
        full_leaf_base_width: full_base_width,
    }
}

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_open<F: Field, EF: ExtensionField<F>>(
    merkle_tree: &RoundMerkleTree<F>,
    index: usize,
) -> (Vec<EF>, Vec<[F; DIGEST_ELEMS]>) {
    if TypeId::of::<(F, EF)>() == TypeId::of::<(Goldilocks, CubicExtensionFieldGL)>() {
        let merkle_tree = unsafe { std::mem::transmute::<_, &RoundMerkleTree<Goldilocks>>(merkle_tree) };
        let (inner_leaf, proof) = merkle_tree.open(index);
        let leaf = CubicExtensionFieldGL::reconstitute_from_base(inner_leaf);
        let leaf = unsafe { std::mem::transmute::<_, Vec<EF>>(leaf) };
        let proof = unsafe { std::mem::transmute::<_, Vec<[F; DIGEST_ELEMS]>>(proof) };
        (leaf, proof)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(Goldilocks, Goldilocks)>() {
        let merkle_tree = unsafe { std::mem::transmute::<_, &RoundMerkleTree<Goldilocks>>(merkle_tree) };
        let (inner_leaf, proof) = merkle_tree.open(index);
        let leaf = Goldilocks::reconstitute_from_base(inner_leaf);
        let leaf = unsafe { std::mem::transmute::<_, Vec<EF>>(leaf) };
        let proof = unsafe { std::mem::transmute::<_, Vec<[F; DIGEST_ELEMS]>>(proof) };
        (leaf, proof)
    } else {
        unimplemented!()
    }
}

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_verify<F: Field, EF: ExtensionField<F>>(
    merkle_root: [F; DIGEST_ELEMS],
    index: usize,
    dimension: Dimensions,
    data: Vec<EF>,
    proof: &Vec<[F; DIGEST_ELEMS]>,
) -> bool {
    let perm = default_goldilocks_poseidon1_8();
    let log_max_height = utils::log2_strict_usize(dimension.height.next_power_of_two());
    if TypeId::of::<(F, EF)>() == TypeId::of::<(Goldilocks, CubicExtensionFieldGL)>() {
        let merkle_root = unsafe { std::mem::transmute_copy::<_, [Goldilocks; DIGEST_ELEMS]>(&merkle_root) };
        let data = unsafe { std::mem::transmute::<_, Vec<CubicExtensionFieldGL>>(data) };
        let proof = unsafe { std::mem::transmute::<_, &Vec<[Goldilocks; DIGEST_ELEMS]>>(proof) };
        let base_data = CubicExtensionFieldGL::flatten_to_base(data);
        symetric::merkle::merkle_verify::<_, _, _, DIGEST_ELEMS, 8, 4>(
            &perm,
            &perm,
            &merkle_root,
            log_max_height,
            index,
            &base_data,
            proof,
        )
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(Goldilocks, Goldilocks)>() {
        let merkle_root = unsafe { std::mem::transmute_copy::<_, [Goldilocks; DIGEST_ELEMS]>(&merkle_root) };
        let data = unsafe { std::mem::transmute::<_, Vec<Goldilocks>>(data) };
        let proof = unsafe { std::mem::transmute::<_, &Vec<[Goldilocks; DIGEST_ELEMS]>>(proof) };
        let base_data = Goldilocks::flatten_to_base(data);
        symetric::merkle::merkle_verify::<_, _, _, DIGEST_ELEMS, 8, 4>(
            &perm,
            &perm,
            &merkle_root,
            log_max_height,
            index,
            &base_data,
            proof,
        )
    } else {
        unimplemented!()
    }
}

#[derive(Debug, Clone)]
pub struct WhirMerkleTree<F, const DIGEST_ELEMS: usize> {
    pub(crate) leaf: Matrix<F, ArenaVec<F>>,
    pub(crate) tree: symetric::merkle::MerkleTree<F, DIGEST_ELEMS>,
    full_leaf_base_width: usize,
}

impl<F: field::PrimeCharacteristicRing + Send + Sync, const DIGEST_ELEMS: usize> WhirMerkleTree<F, DIGEST_ELEMS> {
    #[must_use]
    pub fn root(&self) -> [F; DIGEST_ELEMS] {
        self.tree.root()
    }

    pub fn open(&self, index: usize) -> (Vec<F>, Vec<[F; DIGEST_ELEMS]>) {
        let log_height = log2_ceil_usize(self.leaf.height());
        let mut opening: Vec<F> = self.leaf.row(index).unwrap().collect();
        opening.resize(self.full_leaf_base_width, F::default());
        let proof = self.tree.open_siblings(index, log_height);
        (opening, proof)
    }
}

#[instrument(name = "first digest layer", level = "debug", skip_all)]
fn first_digest_layer_with_initial_state<
    P,
    Perm,
    LV,
    const DIGEST_ELEMS: usize,
    const WIDTH: usize,
    const RATE: usize,
>(
    perm: &Perm,
    matrix: &Matrix<P::Value, LV>,
    packed_initial_state: &[P; WIDTH],
    effective_base_width: usize,
) -> ArenaVec<[P::Value; DIGEST_ELEMS]>
where
    P: PackedValue + Default,
    LV: AsRef<[P::Value]> + Send + Sync,
    P::Value: Default + Copy + Send + Sync,
    Perm: symetric::Permutation<[P::Value; WIDTH]> + symetric::Permutation<[P; WIDTH]>,
{
    let width = P::WIDTH;
    let height = matrix.height();
    assert!(height.is_multiple_of(width));
    let n_pad = (RATE - effective_base_width % RATE) % RATE;

    let mut digests = unsafe { ArenaVec::uninitialized(height) };

    parallel::par_chunks_mut(&mut digests, width, |i, digests_chunk| {
        let first_row = i * width;
        let rtl_iter = matrix.vertically_packed_row_rtl::<P>(first_row, effective_base_width, n_pad);
        let packed_digest: [P; DIGEST_ELEMS] =
            symetric::hash_rtl_iter_with_initial_state::<_, _, _, WIDTH, RATE, DIGEST_ELEMS>(
                perm,
                rtl_iter,
                packed_initial_state,
            );
        for (dst, src) in digests_chunk.iter_mut().zip(unpack_array(packed_digest)) {
            *dst = src;
        }
    });

    digests
}
