/-
# Zeta values at natural arguments

`zetaR s = ∑_{m ≥ 0} 1/(m+1)^s`, the real series of `ζ(s)` (used in Lemma 1).
`riemannZeta_re_eq_zetaR` identifies it with the real part of Mathlib's `riemannZeta` for `s ≥ 2`,
which is how the target statement (`Statement.lean`) is phrased.
-/
import Mathlib

namespace ZetaIrr

open scoped BigOperators

/-- The terms `1/(m+1)^s` of the zeta series. -/
noncomputable def zetaTerm (s : ℕ) (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1) ^ s

/-- `ζ(s) = ∑' m, 1/(m+1)^s` at a natural number `s` (only `s ≥ 2` is used). -/
noncomputable def zetaR (s : ℕ) : ℝ := ∑' m : ℕ, zetaTerm s m

lemma summable_zetaTerm {s : ℕ} (hs : 2 ≤ s) : Summable (zetaTerm s) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (show 1 < s by omega))
  refine h.congr (fun m => ?_)
  simp [zetaTerm]

/-- Mathlib's `riemannZeta` at a natural `s ≥ 2` has real part `zetaR s`. -/
theorem riemannZeta_re_eq_zetaR {s : ℕ} (hs : 2 ≤ s) : (riemannZeta s).re = zetaR s := by
  rw [zeta_nat_eq_tsum_of_gt_one (by omega : 1 < s)]
  have hcast : (fun n : ℕ => 1 / (n : ℂ) ^ s) = fun n : ℕ => (((1 / (n : ℝ) ^ s : ℝ)) : ℂ) := by
    funext n; push_cast; rfl
  rw [hcast, ← Complex.ofReal_tsum, Complex.ofReal_re]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ s) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  rw [hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_pow (show s ≠ 0 by omega), div_zero, zero_add]
  unfold zetaR zetaTerm
  push_cast
  rfl

end ZetaIrr
