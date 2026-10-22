/-
# Stirling along the contour for Z7 (PROOF_ZETA §6.4)

For `x` in the sector region (`‖α_i(x)‖ ≥ a`, `|arg α_i(x)| ≤ π - η`, `α_i(x) = s_i x + u_i`)
and `n = 240(m+1) ≥ 4/a`:

* `Pfun_asymp` (6.4.2, first line): `P_n(nx) = n(2x + 1) exp(λ_n + nΨ(x) + ψ₀(x) + e)`,
  `|e| ≤ 56 (9 + 1/(6 sin²(η/2)))/(a n)`, with `λ_n = -G n log n + G n - 18 log n + 5 log 2π`.

Here `Ψ(x) = Σ c_i α_i log α_i`, `ψ₀(x) = Σ c_i (β_i - 1/2) log α_i` (`Factors.lean`). Only the
`log Γ` Stirling bound is used; no digamma bounds are needed for Z7.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Analytic.Gamma
import ZetaIrrational.Analytic.StirlingSum

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Real Finset Filter Topology
open ZetaIrr.Analytic ZetaIrr.Fam.Analytic

lemma sum_cs_C : ∑ i, (cZ i : ℂ) * sZ i = 0 := by
  have := congrArg (fun r : ℝ => (r : ℂ)) sum_cs; push_cast at this; exact this

lemma sum_cu_C : ∑ i, (cZ i : ℂ) * uZ i = -(547 / 120) := by
  have := congrArg (fun r : ℝ => (r : ℂ)) sum_cu; push_cast at this; exact this

lemma sum_cβ_C : ∑ i, (cZ i : ℂ) * ((βZ i : ℂ) - 1 / 2) = -18 := by
  have := congrArg (fun r : ℝ => (r : ℂ)) sum_cβ; push_cast at this; exact this

lemma sum_c_C : ∑ i, (cZ i : ℂ) = 10 := by
  have := congrArg (fun r : ℝ => (r : ℂ)) sum_c; push_cast at this; exact this

lemma sum_c_alpha (x : ℂ) : ∑ i, (cZ i : ℂ) * alphaZ i x = -(547 / 120) := by
  unfold alphaZ
  simp only [mul_add, sum_add_distrib]
  rw [sum_cu_C]
  have : ∑ i, (cZ i : ℂ) * (sZ i * x) = (∑ i, (cZ i : ℂ) * sZ i) * x := by
    rw [sum_mul]; exact sum_congr rfl (fun i _ => by ring)
  rw [this, sum_cs_C]; ring

lemma sectorHyp_of (a η : ℝ) (x : ℂ) (h : SectorAt a η x) :
    SectorHyp univ (fun i => alphaZ i x) βZ η a :=
  fun i _ => ⟨(h i).1, (h i).2, (βZ_bounds i).1, (βZ_bounds i).2⟩

/-- **(6.4.2)** Stirling for `P_n` along the contour. -/
theorem Pfun_asymp (m : ℕ) {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) {x : ℂ}
    (hx : SectorAt a η x) (hn : 4 / a ≤ (Z7.nOf m : ℝ)) :
    ∃ e : ℂ, ‖e‖ ≤ 56 * ((9 + 1 / (6 * Real.sin (η / 2) ^ 2)) / (a * Z7.nOf m)) ∧
      Pfun m ((Z7.nOf m : ℝ) * x) = ((Z7.nOf m : ℝ) : ℂ) * (2 * x + 1) *
        Complex.exp (lamN (Z7.nOf m) + (Z7.nOf m : ℝ) * PsiZ x + psi0Z x + e) := by
  set n : ℝ := (Z7.nOf m : ℝ) with hn_def
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hS := sectorHyp_of a η x hx
  have hprod := prod_Gamma_zpow_eq_exp univ cZ (fun i => alphaZ i x) βZ hη0 hη ha hS hn
  have hbound := norm_sum_logGamma_sub_main_le univ cZ (fun i => alphaZ i x) βZ hη0 hη ha hS hn
  have hmain := sum_main_eq univ cZ (fun i => alphaZ i x) βZ n
  set e := ∑ i, (cZ i : ℂ) * (Stirling.logGammaS (n * alphaZ i x + βZ i)
    - mainTerm n (alphaZ i x) (βZ i)) with he
  refine ⟨e, ?_, ?_⟩
  · rw [sum_abs_c] at hbound; exact hbound
  have hsplit : ∑ i, (cZ i : ℂ) * Stirling.logGammaS (n * alphaZ i x + βZ i)
      = ∑ i, (cZ i : ℂ) * mainTerm n (alphaZ i x) (βZ i) + e := by
    rw [he, ← sum_add_distrib]; exact sum_congr rfl (fun i _ => by ring)
  have hcβ := sum_cβ_C
  have hc := sum_c_C
  have hca := sum_c_alpha x
  have hΨ : ∑ i, (cZ i : ℂ) * (alphaZ i x * Complex.log (alphaZ i x) - alphaZ i x)
      = PsiZ x + 547 / 120 := by
    rw [show (∑ i, (cZ i : ℂ) * (alphaZ i x * Complex.log (alphaZ i x) - alphaZ i x))
        = PsiZ x - ∑ i, (cZ i : ℂ) * alphaZ i x by
      unfold PsiZ; rw [← sum_sub_distrib]; exact sum_congr rfl (fun i _ => by ring), hca]
    ring
  have hψ : ∑ i, (cZ i : ℂ) * (βZ i - 1 / 2) * Complex.log (alphaZ i x) = psi0Z x := rfl
  have hP : Pfun m ((n : ℂ) * x) = (2 * ((n : ℂ) * x) + n) *
      ∏ i, Complex.Gamma ((n : ℂ) * alphaZ i x + βZ i) ^ cZ i := by
    unfold Pfun
    congr 1
    exact prod_congr rfl (fun i _ => by
      rw [show (sZ i : ℂ) * ((n : ℂ) * x) + (Z7.nOf m : ℂ) * uZ i + βZ i
        = (n : ℂ) * alphaZ i x + βZ i by unfold alphaZ; rw [hn_def]; push_cast; ring])
  rw [hP, hprod, hsplit, hmain, hca, hcβ, hc, hΨ, hψ]
  rw [show (2 * ((n : ℂ) * x) + n) = (n : ℂ) * (2 * x + 1) by ring]
  congr 2
  unfold lamN
  push_cast
  ring

end ZetaIrr.Z7.Analytic
