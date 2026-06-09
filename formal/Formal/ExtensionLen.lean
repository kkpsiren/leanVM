import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Formal.Wrapping

/-!
# The EXTENSION table `len` bound (and the wrapping pair)

Formalizes `§lem:len-bound` of `misc/minimal_zkVM.tex`: on every row `r` of the
EXTENSION table, `len_r ≤ H − r` (as a natural number `< p`), where `H` is the
table height. In particular `len_r ≤ H ≤ 2^21 < p`, which is what makes the
`aux₂` precompile-separator encoding non-wrapping (injective).

The proof is the paper's **backward induction** on `r`, here `Fin.reverseInduction`
(prove the last row, then each row from its successor). It is the first place we
make the **wrapping pair** precise: the `next`-row shift (`§next-mle`) pairs row
`r` with `r+1`, except the last row, which is paired with **itself**
(`wrapNext`). The base case is exactly the degenerate constraint this self-pairing
produces: `(1 − flag_start)·(len − len − 1) = −(1 − flag_start) = 0`, forcing
`flag_start = 1` on the last row.

Modeled over `F = ZMod p` with `p` prime, since the bound is about the canonical
representative `ZMod.val` and the no-overflow step needs `H < p`.
-/

namespace LeanVM

/-- **`len`-bound (`§lem:len-bound`).** Given the EXTENSION-table `len`/`flag_start`
columns over `ZMod p` (`p` prime, height `H = n+1 < p`), and the booleanity,
`len`-countdown, and `len`-boundary constraints (with `wrapNext` as the shift),
every row satisfies `len_r ≤ H − r` as a natural number. -/
theorem len_bound {p : ℕ} [Fact (Nat.Prime p)] {n : ℕ} (hHp : n + 1 < p)
    (len flag_start : Fin (n + 1) → ZMod p)
    (hbool : ∀ r, flag_start r * (1 - flag_start r) = 0)
    (hcount : ∀ r, (1 - flag_start (wrapNext r)) * (len r - len (wrapNext r) - 1) = 0)
    (hbound : ∀ r, flag_start (wrapNext r) * (len r - 1) = 0)
    (r : Fin (n + 1)) : (len r).val ≤ n + 1 - r.val := by
  haveI : Fact (1 < p) := ⟨(Fact.out : Nat.Prime p).one_lt⟩
  induction r using Fin.reverseInduction with
  | last =>
      -- Wrapping pair: the countdown constraint degenerates and forces flag_start = 1.
      have hc := hcount (Fin.last n)
      rw [wrapNext_last] at hc
      have hfs : flag_start (Fin.last n) = 1 := by
        have h1 : (1 - flag_start (Fin.last n)) * (-1 : ZMod p) = 0 := by
          linear_combination hc
        rcases mul_eq_zero.mp h1 with h | h
        · linear_combination -h
        · exact absurd (neg_eq_zero.mp h) one_ne_zero
      have hb := hbound (Fin.last n)
      rw [wrapNext_last, hfs, one_mul] at hb
      have hlen : len (Fin.last n) = 1 := by linear_combination hb
      rw [hlen, Fin.val_last, ZMod.val_one]
      omega
  | cast i IH =>
      have hi := i.isLt
      have hns := wrapNext_castSucc i
      -- flag_start of the successor row is boolean.
      rcases mul_eq_zero.mp (hbool i.succ) with h | h
      · -- successor is not a group start: len counts down by one.
        have hc := hcount i.castSucc
        rw [hns, h, sub_zero, one_mul] at hc
        have hlen : len i.castSucc = len i.succ + 1 := by linear_combination hc
        have hvalsucc : (len i.succ).val ≤ n - i.val := by
          have h2 := IH; rw [Fin.val_succ] at h2; omega
        have hbnd : (len i.succ).val + 1 < p := by omega
        rw [Fin.val_castSucc, hlen, ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hbnd]
        omega
      · -- successor starts a new group: current row is the group's last element.
        have hfs : flag_start i.succ = 1 := by linear_combination -h
        have hb := hbound i.castSucc
        rw [hns, hfs, one_mul] at hb
        have hlen : len i.castSucc = 1 := by linear_combination hb
        rw [Fin.val_castSucc, hlen, ZMod.val_one]
        omega

end LeanVM
