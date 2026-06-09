import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# The wrapping pair

The AIR `next`-row shift (`misc/minimal_zkVM.tex`, §next-mle) over a committed
table of `H = n+1` rows pairs row `r` with row `r+1`, **except the last row,
which is paired with itself**. `wrapNext` is that index map. It is shared by
every table (EXECUTION, EXTENSION, …): a constraint stated as "holds on every
row `r`, with `next = wrapNext r`" is the faithful form of what the zerocheck /
sumcheck establishes, and `wrapNext_castSucc` lets us read off the ordinary
consecutive-pair `(r, r+1)` constraints from it.
-/

namespace LeanVM

/-- The "next row" index with the wrapping pair: row `r` is paired with `r + 1`,
except the last row `n`, which is paired with itself. -/
def wrapNext {n : ℕ} (r : Fin (n + 1)) : Fin (n + 1) :=
  if h : (r : ℕ) + 1 < n + 1 then ⟨r + 1, h⟩ else r

@[simp] theorem wrapNext_last {n : ℕ} : wrapNext (Fin.last n) = Fin.last n := by
  unfold wrapNext
  rw [dif_neg]
  simp [Fin.val_last]

theorem wrapNext_castSucc {n : ℕ} (i : Fin n) : wrapNext i.castSucc = i.succ := by
  unfold wrapNext
  rw [dif_pos]
  · apply Fin.ext
    simp [Fin.val_succ]
  · simp only [Fin.val_castSucc]
    omega

end LeanVM
