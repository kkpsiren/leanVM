import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Poseidon: the sparse partial-round optimization encodes the vanilla permutation

The POSEIDON table's AIR computes the partial rounds in a **sparse** form
(`crates/lean_vm/src/tables/poseidon/mod.rs`, `sparse_mat_air_16`): a one-time
dense matrix `M_I`, then per round a lane-0 S-box followed by multiplication by a
*sparse* matrix (dense first row, a `v`-column, identity elsewhere). The
**vanilla** Poseidon1 (`crates/lean_prover/python-verifier/primitives.py`,
`Poseidon1.permute`) instead applies, every partial round, the lane-0 S-box
followed by the *dense circulant MDS*.

This file formalizes the algebraic mechanism that makes the two equal — the
content of `_compute_sparse_constants` (Appendix B of the Poseidon paper). The
partial-round S-box touches only lane 0, so each dense MDS factors as `M = S · D`
where `D` **fixes lane 0** (acts as the identity on lane 0, both as a row and a
column). The key fact:

> a lane-0-fixing matrix `D` **commutes with the lane-0 S-box** (`mulVec_sbox0_comm`),

lets the `D` factor be pushed *through* the S-box (`round_pushThrough`) into the
adjacent round. Iterating, all the `D` factors collapse to the single boundary
matrix `M_I`, leaving the sparse `S`-matrices inline — which is precisely the
sparse AIR.

`partial_rounds_sparse` proves this for **all** `R` partial rounds: the vanilla
dense-MDS partial-round phase equals the sparse chain produced by a factorization
oracle (the abstract form of `_compute_sparse_constants`, which supplies, for each
carried boundary, the per-round sparse matrix and the next boundary). The two
remaining ingredients are not formalized here: (i) the round-constant compression
(`scalar_rc` / `sparse_first_round_constants`), a separable affine layer; and
(ii) the concrete KoalaBear 16×16 MDS and 20-round factorization data — that is
the numeric instance, this is the mechanism. The full rounds are identical in
both forms (both apply the dense MDS), so only the partial phase needs this
argument.
-/

namespace LeanVM

open Matrix

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The lane-0 S-box: apply `σ` to coordinate `0`, leave the rest. For Poseidon,
`σ = (· ^ 3)`. -/
def sbox0 (σ : K → K) (s : Fin (n + 1) → K) : Fin (n + 1) → K :=
  Function.update s 0 (σ (s 0))

omit [CommRing K] in
@[simp] theorem sbox0_apply_zero (σ : K → K) (s : Fin (n + 1) → K) :
    sbox0 σ s 0 = σ (s 0) := by
  simp [sbox0]

omit [CommRing K] in
theorem sbox0_apply_ne (σ : K → K) (s : Fin (n + 1) → K) {i : Fin (n + 1)}
    (hi : i ≠ 0) : sbox0 σ s i = s i := by
  simp [sbox0, Function.update_of_ne hi]

/-- A matrix **fixes lane 0** when its first row and first column are the standard
basis vector `e₀`: it leaves coordinate `0` unchanged and never feeds coordinate
`0` into the other coordinates. (This is the form of the `D` factors in the
Poseidon partial-round decomposition.) -/
structure FixesLane0 (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : Prop where
  row0 : ∀ j, M 0 j = if j = 0 then 1 else 0
  col0 : ∀ i, M i 0 = if i = 0 then 1 else 0

/-- A matrix whose first row is `e₀` leaves coordinate `0` unchanged under
`mulVec`. -/
theorem mulVec_lane0 {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (h : ∀ j, M 0 j = if j = 0 then 1 else 0) (x : Fin (n + 1) → K) :
    (M *ᵥ x) 0 = x 0 := by
  show ∑ j, M 0 j * x j = x 0
  simp only [h, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

/-- **The commutation lemma (heart of the sparse optimization).** A lane-0-fixing
matrix commutes with the lane-0 S-box. -/
theorem mulVec_sbox0_comm (σ : K → K) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hM : FixesLane0 M) (s : Fin (n + 1) → K) :
    M *ᵥ sbox0 σ s = sbox0 σ (M *ᵥ s) := by
  funext i
  rcases eq_or_ne i 0 with rfl | hi
  · -- lane 0: both sides equal `σ (s 0)`.
    rw [mulVec_lane0 hM.row0, sbox0_apply_zero, sbox0_apply_zero, mulVec_lane0 hM.row0]
  · -- lane `i ≠ 0`: the S-box is invisible here and `M` ignores coordinate 0.
    rw [sbox0_apply_ne σ (M *ᵥ s) hi]
    show ∑ j, M i j * sbox0 σ s j = ∑ j, M i j * s j
    apply Finset.sum_congr rfl
    intro j _
    rcases eq_or_ne j 0 with rfl | hj
    · rw [hM.col0 i, if_neg hi]; ring
    · rw [sbox0_apply_ne σ s hj]

/-- **One round, factored.** If a dense round matrix factors as `M = S · D` with
`D` fixing lane 0, then the dense round equals the sparse round `S` applied after
pushing `D` through the S-box. This is the per-round step of the optimization:
`D` moves left (towards the boundary), `S` stays inline. -/
theorem round_pushThrough (σ : K → K)
    {S D M : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hD : FixesLane0 D) (hM : M = S * D) (x : Fin (n + 1) → K) :
    M *ᵥ sbox0 σ x = S *ᵥ sbox0 σ (D *ᵥ x) := by
  rw [hM, ← mulVec_mulVec, mulVec_sbox0_comm σ hD]

/-- **Two rounds telescoping.** With the iterated factorization `M = S₁·D₁` and
`D₁·M = S₂·D₂`, two dense partial rounds equal two sparse rounds applied after the
boundary matrix `D₂` — the lane-0-fixing factors have collapsed to the front.
Iterating this across all 20 partial rounds turns the dense MDS rounds into the
sparse AIR (`M_I` = the accumulated boundary). -/
theorem two_round_push (σ : K → K)
    {M S₁ D₁ S₂ D₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hD₁ : FixesLane0 D₁) (hD₂ : FixesLane0 D₂)
    (h1 : M = S₁ * D₁) (h2 : D₁ * M = S₂ * D₂) (s : Fin (n + 1) → K) :
    M *ᵥ sbox0 σ (M *ᵥ sbox0 σ s)
      = S₁ *ᵥ sbox0 σ (S₂ *ᵥ sbox0 σ (D₂ *ᵥ s)) := by
  rw [round_pushThrough σ hD₁ h1, mulVec_mulVec, round_pushThrough σ hD₂ h2]

/-! ## The full partial-round phase

The `R`-fold telescoping of `two_round_push`. A **factorization oracle** `factor`
maps each lane-0-fixing boundary `B` to a pair `(S, B')` with `B · M = S · B'` and
`B'` again lane-0-fixing — exactly the data `_compute_sparse_constants` produces
numerically (`S` = the per-round sparse matrix, `B'` = the carried boundary; the
final boundary is `M_I`). `sparseChain` runs the sparse rounds the oracle defines;
`partial_rounds_sparse` proves the dense partial-round phase equals it. -/

/-- The sparse partial-round computation defined by a factorization oracle:
starting from boundary `B`, each of the `R` rounds applies the lane-0 S-box and
the oracle's sparse matrix, carrying the boundary forward. -/
def sparseChain (σ : K → K)
    (factor : Matrix (Fin (n + 1)) (Fin (n + 1)) K →
      Matrix (Fin (n + 1)) (Fin (n + 1)) K × Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K → ℕ → (Fin (n + 1) → K) → (Fin (n + 1) → K)
  | B, 0, x => B *ᵥ x
  | B, R + 1, x => (factor B).1 *ᵥ sbox0 σ (sparseChain σ factor (factor B).2 R x)

/-- **Telescoping.** For any lane-0-fixing boundary `B`, applying `B` after `R`
dense partial rounds equals the sparse chain the oracle defines from `B`. The
`D`-factors are pushed through the S-boxes (`mulVec_sbox0_comm`) and accumulate
into the carried boundary. -/
theorem telescope (σ : K → K) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (factor : Matrix (Fin (n + 1)) (Fin (n + 1)) K →
      Matrix (Fin (n + 1)) (Fin (n + 1)) K × Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hfac : ∀ B, FixesLane0 B →
      B * M = (factor B).1 * (factor B).2 ∧ FixesLane0 (factor B).2) :
    ∀ (R : ℕ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) K), FixesLane0 B →
      ∀ x, B *ᵥ (fun y => M *ᵥ sbox0 σ y)^[R] x = sparseChain σ factor B R x := by
  intro R
  induction R with
  | zero => intro B _ x; rfl
  | succ R ih =>
      intro B hB x
      obtain ⟨hBM, hB'⟩ := hfac B hB
      simp only [Function.iterate_succ_apply']
      rw [mulVec_mulVec, hBM, ← mulVec_mulVec, mulVec_sbox0_comm σ hB',
        ih (factor B).2 hB']
      rfl

/-- The identity matrix fixes lane 0. -/
theorem one_fixesLane0 : FixesLane0 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) where
  row0 j := by rw [Matrix.one_apply]; exact if_congr eq_comm rfl rfl
  col0 i := by rw [Matrix.one_apply]

/-- **The sparse partial rounds encode the vanilla partial rounds.** The vanilla
partial-round phase — `R` applications of `s ↦ M *ᵥ sbox0 σ s` with the dense MDS
`M` — equals the sparse chain produced by the factorization oracle, started from
the identity boundary (whose final accumulated boundary is `M_I`). -/
theorem partial_rounds_sparse (σ : K → K)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (factor : Matrix (Fin (n + 1)) (Fin (n + 1)) K →
      Matrix (Fin (n + 1)) (Fin (n + 1)) K × Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hfac : ∀ B, FixesLane0 B →
      B * M = (factor B).1 * (factor B).2 ∧ FixesLane0 (factor B).2)
    (R : ℕ) (x : Fin (n + 1) → K) :
    (fun y => M *ᵥ sbox0 σ y)^[R] x = sparseChain σ factor 1 R x := by
  have h := telescope σ factor hfac R 1 one_fixesLane0 x
  rwa [Matrix.one_mulVec] at h

end LeanVM
