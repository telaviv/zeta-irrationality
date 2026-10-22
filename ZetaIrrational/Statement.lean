/-
# The target statement

`OneOfZeta7To21`: at least one of ζ(7), ζ(9), …, ζ(21) is irrational, stated with Mathlib's
`riemannZeta` (as in domino14/zeta5's `Claim.lean`).

Proved here: the reduction of the statement to the existence of small integer linear forms in
`zetaR 7, zetaR 9, …, zetaR 21` that are nonzero infinitely often (PROOF_ZETA §7, the
contradiction step). The forms are constructed and bounded in `FamilyZ7.lean` and `Z7/`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Defs
import ZetaIrrational.Criterion

namespace ZetaIrr

open Filter Topology
open scoped BigOperators

/-- **The main statement.** At least one of `ζ(7), ζ(9), …, ζ(21)` is irrational, where `ζ` is
Mathlib's `riemannZeta`. -/
def OneOfZeta7To21 : Prop :=
  ∃ j ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), Irrational (riemannZeta j).re

lemma zeta_index_set : ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ)
    = (Finset.Icc 3 10).image (fun j => 2 * j + 1) := by decide

/-- Small integer linear forms `a n + ∑_{j=3}^{10} c n j ζ(2j+1)` that are nonzero infinitely
often prove `OneOfZeta7To21`. -/
theorem oneOfZeta7To21_of_forms (a : ℕ → ℤ) (c : ℕ → ℕ → ℤ)
    (hlim : Tendsto
      (fun n => (a n : ℝ) + ∑ j ∈ Finset.Icc 3 10, (c n j : ℝ) * zetaR (2 * j + 1))
      atTop (𝓝 0))
    (hne : ∃ᶠ n in atTop,
      (a n : ℝ) + ∑ j ∈ Finset.Icc 3 10, (c n j : ℝ) * zetaR (2 * j + 1) ≠ 0) :
    OneOfZeta7To21 := by
  obtain ⟨j, hj, hirr⟩ :=
    exists_irrational_of_small_forms (Finset.Icc 3 10) (fun j => zetaR (2 * j + 1)) a c hlim hne
  refine ⟨2 * j + 1, ?_, ?_⟩
  · rw [zeta_index_set]; exact Finset.mem_image_of_mem _ hj
  · have h2 : 2 ≤ 2 * j + 1 := by simp only [Finset.mem_Icc] at hj; omega
    rw [riemannZeta_re_eq_zetaR h2]; exact hirr

end ZetaIrr
