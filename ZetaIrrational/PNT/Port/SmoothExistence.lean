/-
Ported from PrimeNumberTheoremAnd (A. Kontorovich, T. Tao, et al.),
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd, commit a5154676af9aa3095150ee410cdda80555aa0642,
file `PrimeNumberTheoremAnd/SmoothExistence.lean`. Licensed under the Apache License 2.0 (see `LICENSE` in this
directory). Changes: blueprint annotations removed, declarations wrapped in
`namespace Zeta5.PNTPort`, unused declarations removed, and adaptations to a newer Mathlib.

Second-hand port: copied from the `Zeta5/Zeta5/PNTPort/` directory of domino14/zeta5 (commit
3da8eb1b91f9a90a1c0b7959e845c060dbd16256, Lean v4.35.0-rc2), which made the changes listed above.
Further changes here: namespace `Zeta5.PNTPort` renamed to `ZetaIrr.PNT.Port`, imports re-pointed
(no other source changes were needed for Mathlib v4.35.0). The Apache-2.0 `LICENSE` is reproduced in
this directory.
-/
import Batteries.Tactic.Lemma
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Bound

namespace ZetaIrr.PNT.Port


set_option lang.lemmaCmd true

open MeasureTheory Set Real

open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]


end ZetaIrr.PNT.Port
