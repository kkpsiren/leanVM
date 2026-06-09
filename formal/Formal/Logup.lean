import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
# The logup non-vanishing lemma (the deterministic heart of bus balance)

`Formal/Bus.lean` takes bus **balance** as a hypothesis — the verified output of
the logup-GKR protocol. This file formalizes the deterministic core of *why* the
logup identity forces balance, following `misc/minimal_zkVM.tex`
§"Balanced bus proved via logup" (lines 730–742) and S-two's `count_eq_of_sum_eq'`.

The bus is balanced iff, for every tuple `σ`, the net signed multiplicity
`M(σ) = ∑_{k : σ_k = σ} m_k` is zero (pushes `+`, pulls `−`). Fingerprinting the
(distinct) tuples to field values `v_σ` and clearing denominators turns the logup
rational identity `∑_σ M(σ)/(γ − v_σ) = 0` into the polynomial identity `N = 0`,
where
`N(X) = ∑_σ M(σ) · ∏_{σ' ≠ σ} (X − v_{σ'})`.
The tex proves: if some `M(σ) ≠ 0` then `N ≠ 0`. We prove the contrapositive
`N = 0 ⟹ ∀ σ, M(σ) = 0` — i.e. the support is empty, the bus is balanced.

## Boundary

This is the *deterministic* step. The surrounding logup-GKR pieces remain the
trust boundary (as the tex itself frames them, "up to soundness error `K·ℓ/q`"):
the rational identity `⟹ N = 0` (cross-multiplication); `N = 0` at a single
Fiat–Shamir-random point `⟹ N = 0` as a polynomial (Schwartz–Zippel, degree
`≤ K·ℓ`); and the fingerprint `π_β` being injective on the present tuples
(collision probability `≤ ℓ/q`). Composing this lemma with those gives the
`Bus.Balanced` that `Formal/Bus.lean` assumes.
-/

namespace LeanVM

open Polynomial Finset

/-- **Logup non-vanishing (`§Balanced bus`, contrapositive).** For an indexed
family of **distinct** field values `v` and coefficients `c` (the net signed
multiplicities), if the logup numerator polynomial
`∑ᵢ cᵢ · ∏_{j ≠ i} (X − vⱼ)` is the zero polynomial, then every `cᵢ = 0`. -/
theorem logup_vanishing {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → F) (hv : Function.Injective v) (c : ι → F)
    (hN : (∑ i, C (c i) * ∏ j ∈ univ.erase i, (X - C (v j))) = 0) :
    ∀ i, c i = 0 := by
  intro i₀
  -- Evaluate the numerator identity at `X = v i₀`.
  have heval := congrArg (eval (v i₀)) hN
  rw [eval_zero, eval_finsetSum] at heval
  simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X] at heval
  -- heval : ∑ i, c i * ∏ j ∈ univ.erase i, (v i₀ - v j) = 0
  -- Every term with `i ≠ i₀` vanishes: its product contains the factor `v i₀ − v i₀`.
  have h₀ : ∀ b ∈ (univ : Finset ι), b ≠ i₀ →
      c b * ∏ j ∈ univ.erase b, (v i₀ - v j) = 0 := by
    intro b _ hb
    apply mul_eq_zero_of_right
    refine Finset.prod_eq_zero (i := i₀) ?_ ?_
    · rw [mem_erase]; exact ⟨hb.symm, mem_univ i₀⟩
    · rw [sub_self]
  rw [Finset.sum_eq_single_of_mem i₀ (mem_univ i₀) h₀] at heval
  -- heval : c i₀ * ∏ j ∈ univ.erase i₀, (v i₀ - v j) = 0
  -- The surviving product is nonzero (the values are distinct), so `c i₀ = 0`.
  have hprod : (∏ j ∈ univ.erase i₀, (v i₀ - v j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [sub_ne_zero]
    intro hcontra
    exact (mem_erase.mp hj).1 (hv hcontra).symm
  exact (mul_eq_zero.mp heval).resolve_right hprod

end LeanVM
