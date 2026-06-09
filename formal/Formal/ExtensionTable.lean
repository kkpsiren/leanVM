import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# Soundness of the EXTENSION table accumulation (core content)

This file formalizes the heart of the EXTENSION table (`misc/minimal_zkVM.tex`,
§"EXTENSION table"): the **multi-row group accumulation**. Each `EXTENSION_OP`
of length `N` occupies `N` consecutive rows, and the `acc` column accumulates
*backward* — the last row holds a single element's contribution, each earlier
row folds in its own, and the group-start row holds the full result `res`. We
prove this telescoping is sound: `res` equals the intended aggregate of the
per-element operations.

* `ADD`     : `res = ∑ᵢ (aᵢ + bᵢ)`               (additive accumulation)
* `DOT_PRODUCT` : `res = ∑ᵢ (aᵢ · bᵢ)`           (additive accumulation)
* `EQ`      : `res = ∏ᵢ eqHat(aᵢ, bᵢ)`            (multiplicative accumulation)

Everything is over an abstract commutative ring `K`, instantiated by the
extension field `Fq = F[X]/(X⁵+X²−1)` (`§Field`). The aggregation is
ring-agnostic, so working over abstract `K` is both cleaner and more general;
each `K`-equation stands for the `DIMENSION = 5` coordinate-wise base-field
constraints of the spec.

## Scope / boundary

The operands `a b : Fin (n+1) → K` are the *already-resolved* per-element
extension values `(ṽ_A⁽ⁱ⁾, v_B⁽ⁱ⁾)`. Recovering them from the committed
base-field columns — the `embed` map, the base×extension (`flag_be`) vs
extension×extension distinction, and the strided memory reads `idx_A`/`idx_B` —
is the memory-binding layer, discharged via the bus exactly as for the EXECUTION
table (`Formal/Bus.lean`). The intra-group bookkeeping (the `len` countdown and
`§lem:len-bound` wrapping-pair argument, which bound `len ≤ 2^21` so the `aux₂`
domain separator does not wrap) is likewise deferred; here we take the
accumulation recurrence in the clean per-group form the bookkeeping establishes.
-/

namespace LeanVM

variable {K : Type*}

/-! ## Telescoping lemmas

These say: a column `acc` satisfying the backward recurrence the AIR imposes
(last row `= eₗₐₛₜ`; each earlier row `= eᵢ ⋆ acc(i+1)`) has its group-start
entry `acc 0` equal to the aggregate `⋆ᵢ eᵢ`. -/

/-- **Additive telescoping** (`ADD`, `DOT_PRODUCT`): the backward additive
recurrence makes the group-start accumulator the full sum. -/
theorem sum_of_acc [AddCommMonoid K] :
    ∀ {n : ℕ} (e acc : Fin (n + 1) → K),
      acc (Fin.last n) = e (Fin.last n) →
      (∀ i : Fin n, acc i.castSucc = e i.castSucc + acc i.succ) →
      acc 0 = ∑ i, e i := by
  intro n
  induction n with
  | zero =>
      intro e acc hlast _
      rw [Fin.sum_univ_one]
      simpa using hlast
  | succ m ih =>
      intro e acc hlast hstep
      have hlast' : acc (Fin.last m).succ = e (Fin.last m).succ := by
        rw [Fin.succ_last]; exact hlast
      have hstep' : ∀ j : Fin m,
          acc j.castSucc.succ = e j.castSucc.succ + acc j.succ.succ := by
        intro j
        have h := hstep j.succ
        rwa [Fin.castSucc_succ] at h
      have key := ih (fun j => e j.succ) (fun j => acc j.succ) hlast' hstep'
      rw [Fin.sum_univ_succ, ← key]
      have h0 := hstep 0
      simpa using h0

/-- **Multiplicative telescoping** (`EQ`): the backward multiplicative recurrence
makes the group-start accumulator the full product. -/
theorem prod_of_acc [CommMonoid K] :
    ∀ {n : ℕ} (e acc : Fin (n + 1) → K),
      acc (Fin.last n) = e (Fin.last n) →
      (∀ i : Fin n, acc i.castSucc = e i.castSucc * acc i.succ) →
      acc 0 = ∏ i, e i := by
  intro n
  induction n with
  | zero =>
      intro e acc hlast _
      rw [Fin.prod_univ_one]
      simpa using hlast
  | succ m ih =>
      intro e acc hlast hstep
      have hlast' : acc (Fin.last m).succ = e (Fin.last m).succ := by
        rw [Fin.succ_last]; exact hlast
      have hstep' : ∀ j : Fin m,
          acc j.castSucc.succ = e j.castSucc.succ * acc j.succ.succ := by
        intro j
        have h := hstep j.succ
        rwa [Fin.castSucc_succ] at h
      have key := ih (fun j => e j.succ) (fun j => acc j.succ) hlast' hstep'
      rw [Fin.prod_univ_succ, ← key]
      have h0 := hstep 0
      simpa using h0

/-! ## Per-operation soundness

In each theorem `a b : Fin (n+1) → K` are the resolved per-element operands, `acc`
is the committed accumulator column, and `res` the committed result. `hres` is
the group-start constraint `flag_start · (acc − res) = 0`; `hlast`/`hstep` are the
per-row accumulation constraint specialized to the last row (`acc_tail = 0`) and
to an interior row (`acc_tail = next(acc)`). -/

/-- The pointwise equality kernel `eqHat(a, b) = a·b + (1−a)(1−b)` (§AIR
constraints, `e_eq`). -/
def eqHat [CommRing K] (a b : K) : K := a * b + (1 - a) * (1 - b)

/-- **`ADD` soundness:** the table computes `res = ∑ᵢ (aᵢ + bᵢ)`. -/
theorem ext_add_sound [CommRing K] {n : ℕ} (a b acc : Fin (n + 1) → K) (res : K)
    (hres : res = acc 0)
    (hlast : acc (Fin.last n) = a (Fin.last n) + b (Fin.last n))
    (hstep : ∀ i : Fin n,
      acc i.castSucc = (a i.castSucc + b i.castSucc) + acc i.succ) :
    res = ∑ i, (a i + b i) := by
  rw [hres]; exact sum_of_acc (fun i => a i + b i) acc hlast hstep

/-- **`DOT_PRODUCT` soundness:** the table computes `res = ∑ᵢ (aᵢ · bᵢ)`. -/
theorem ext_dot_sound [CommRing K] {n : ℕ} (a b acc : Fin (n + 1) → K) (res : K)
    (hres : res = acc 0)
    (hlast : acc (Fin.last n) = a (Fin.last n) * b (Fin.last n))
    (hstep : ∀ i : Fin n,
      acc i.castSucc = (a i.castSucc * b i.castSucc) + acc i.succ) :
    res = ∑ i, (a i * b i) := by
  rw [hres]; exact sum_of_acc (fun i => a i * b i) acc hlast hstep

/-- **`EQ` soundness:** the table computes `res = ∏ᵢ eqHat(aᵢ, bᵢ)`. -/
theorem ext_eq_sound [CommRing K] {n : ℕ} (a b acc : Fin (n + 1) → K) (res : K)
    (hres : res = acc 0)
    (hlast : acc (Fin.last n) = eqHat (a (Fin.last n)) (b (Fin.last n)))
    (hstep : ∀ i : Fin n,
      acc i.castSucc = eqHat (a i.castSucc) (b i.castSucc) * acc i.succ) :
    res = ∏ i, eqHat (a i) (b i) := by
  rw [hres]; exact prod_of_acc (fun i => eqHat (a i) (b i)) acc hlast hstep

end LeanVM
