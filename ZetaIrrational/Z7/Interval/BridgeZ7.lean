/-
# Bridge: the Z7 interval certificate in the vocabulary of `Z7/Analytic/`

`Z7/Analytic/Factors.lean` indexes the Z7 factor list by `Fin 40` (`cZ`, `sZ`, `uZ`,
`alphaZ`) and defines `PsiZ`, `Psi1Z`, `Psi2Z`, `Psi3Z`, `phaseZ`, `SectorAt`. This file proves that
they agree with the list-based `Ψ`, `dpsiL`, `d2psiL`, `d3psiL`, `f` of the interval certificate
(through the enumeration `facA` of `facZ7` and the generic `Fam/Interval/ListSum.lean`), and
restates the certified saddle data (S0)–(S5) in those terms.
-/
import ZetaIrrational.Z7.Interval.ContourZ7
import ZetaIrrational.Z7.Analytic.Factors
import ZetaIrrational.Fam.Interval.ListSum

namespace ZetaIrr.Z7.Interval

open Complex Metric Real ZetaIrr.Interval ZetaIrr.Fam.Interval
open ZetaIrr.Z7.Analytic (cZ sZ uZ alphaZ PsiZ Psi1Z Psi2Z Psi3Z phaseZ SectorAt)

/-- The factor list in the `Z7/Analytic/` order (the same order as `facZ7`). -/
def facA : Fin 40 → Fac :=
  ![⟨5, 1, 0⟩, ⟨5, -1, 11 / 12⟩, ⟨5, 1, 23 / 12⟩, ⟨-5, 1, 1⟩,
    ⟨1, 1, 1 / 80⟩, ⟨-1, 1, 79 / 80⟩, ⟨1, 1, 2 / 80⟩, ⟨-1, 1, 78 / 80⟩,
    ⟨1, 1, 3 / 80⟩, ⟨-1, 1, 77 / 80⟩, ⟨1, 1, 4 / 80⟩, ⟨-1, 1, 76 / 80⟩,
    ⟨1, 1, 5 / 80⟩, ⟨-1, 1, 75 / 80⟩, ⟨1, 1, 6 / 80⟩, ⟨-1, 1, 74 / 80⟩,
    ⟨1, 1, 7 / 80⟩, ⟨-1, 1, 73 / 80⟩, ⟨1, 1, 8 / 80⟩, ⟨-1, 1, 72 / 80⟩,
    ⟨1, 1, 9 / 80⟩, ⟨-1, 1, 71 / 80⟩, ⟨1, 1, 10 / 80⟩, ⟨-1, 1, 70 / 80⟩,
    ⟨1, 1, 11 / 80⟩, ⟨-1, 1, 69 / 80⟩, ⟨1, 1, 12 / 80⟩, ⟨-1, 1, 68 / 80⟩,
    ⟨1, 1, 13 / 80⟩, ⟨-1, 1, 67 / 80⟩, ⟨1, 1, 14 / 80⟩, ⟨-1, 1, 66 / 80⟩,
    ⟨1, 1, 15 / 80⟩, ⟨-1, 1, 65 / 80⟩, ⟨1, 1, 16 / 80⟩, ⟨-1, 1, 64 / 80⟩,
    ⟨1, 1, 17 / 80⟩, ⟨-1, 1, 63 / 80⟩, ⟨1, 1, 18 / 80⟩, ⟨-1, 1, 62 / 80⟩]

lemma ofFn_facA : List.ofFn facA = facZ7 := by decide +kernel

lemma facA_mem (i : Fin 40) : facA i ∈ facZ7 := by
  rw [← ofFn_facA]; exact List.mem_ofFn.2 ⟨i, rfl⟩

lemma facA_c : ∀ i, (facA i).c = cZ i := by decide +kernel

lemma facA_s (i : Fin 40) : (((facA i).s : ℤ) : ℝ) = sZ i := by
  fin_cases i <;> simp [facA, sZ]

lemma facA_κ (i : Fin 40) : (((facA i).κ : ℚ) : ℝ) = uZ i := by
  fin_cases i <;> simp [facA, uZ]

lemma facA_sC (i : Fin 40) : ((facA i).s : ℂ) = ((sZ i : ℝ) : ℂ) := by
  rw [← facA_s]; push_cast; rfl

lemma facA_κC (i : Fin 40) : ((facA i).κ : ℂ) = ((uZ i : ℝ) : ℂ) := by
  rw [← facA_κ]; push_cast; rfl

lemma facA_cC (i : Fin 40) : ((facA i).c : ℂ) = ((cZ i : ℤ) : ℂ) := by rw [facA_c]

lemma alphaZ_eq (i : Fin 40) (x : ℂ) : alphaZ i x = (facA i).α x := by
  simp only [alphaZ, Fac.α, facA_sC, facA_κC]

theorem alphaZ_mem (i : Fin 40) (x : ℂ) : ∃ a ∈ facZ7, alphaZ i x = a.α x :=
  ⟨facA i, facA_mem i, alphaZ_eq i x⟩

theorem PsiZ_eq (x : ℂ) : PsiZ x = Ψ x := by
  have h := sum_fin_eq_list facA (fun a => (a.c : ℂ) * (a.α x * log (a.α x)))
  rw [ofFn_facA, ← psiL_eq_sum] at h
  rw [Ψ, ← h, PsiZ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [alphaZ_eq, facA_cC]

theorem Psi1Z_eq (x : ℂ) : Psi1Z x = dpsiL facZ7 x := by
  have hcs : ∑ i, ((cZ i : ℂ) * ((sZ i : ℝ) : ℂ)) = 0 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) ZetaIrr.Z7.Analytic.sum_cs
    push_cast at this; exact this
  have h := sum_fin_eq_list facA (fun a => (a.c : ℂ) * ((a.s : ℂ) * (log (a.α x) + 1)))
  rw [ofFn_facA, ← dpsiL_eq_sum] at h
  rw [← h]
  calc Psi1Z x = Psi1Z x + ∑ i, ((cZ i : ℂ) * ((sZ i : ℝ) : ℂ)) := by rw [hcs, add_zero]
    _ = ∑ i, ((cZ i : ℂ) * ((sZ i : ℝ) : ℂ) * log (alphaZ i x)
          + (cZ i : ℂ) * ((sZ i : ℝ) : ℂ)) := by
        rw [Psi1Z, ← Finset.sum_add_distrib]
    _ = _ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [alphaZ_eq, facA_cC, facA_sC]; ring

theorem Psi2Z_eq (x : ℂ) : Psi2Z x = d2psiL facZ7 x := by
  have h := sum_fin_eq_list facA (fun a => (a.c : ℂ) * ((a.s : ℂ) * (a.s : ℂ) / a.α x))
  rw [ofFn_facA, ← d2psiL_eq_sum] at h
  rw [← h, Psi2Z]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [alphaZ_eq, facA_cC, facA_sC]; ring

theorem Psi3Z_eq (x : ℂ) : Psi3Z x = d3psiL facZ7 x := by
  have h := sum_fin_eq_list facA
    (fun a => (a.c : ℂ) * (-((a.s : ℂ) * (a.s : ℂ) * (a.s : ℂ)) / a.α x ^ 2))
  rw [ofFn_facA, ← d3psiL_eq_sum] at h
  rw [← h, Psi3Z, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [alphaZ_eq, facA_cC, facA_sC]; ring

theorem phaseZ_eq (x : ℂ) : phaseZ x = f x := by
  rw [phaseZ, f_apply, PsiZ_eq]

/-- The sector condition of `Z7/Analytic/` from the list form, with `a = 1/100`,
`η = π - 2.76 > 0.38`. -/
theorem sectorAt_of {x : ℂ}
    (h : ∀ a ∈ facZ7, ((amin : ℚ) : ℝ) ≤ ‖a.α x‖ ∧ |arg (a.α x)| ≤ ((Amax : ℚ) : ℝ)) :
    SectorAt (1 / 100) (π - 276 / 100) x := by
  intro i
  obtain ⟨a, ha, e⟩ := alphaZ_mem i x
  rw [e]
  have := h a ha
  constructor
  · have h1 := this.1; norm_num [amin] at h1; exact h1
  · have h2 := this.2; norm_num [Amax] at h2; linarith

theorem eta_pos : (38 / 100 : ℝ) < π - 276 / 100 := by
  have := Real.pi_gt_d2; linarith

/-! ## (S0)/(S1) in `Z7/Analytic/` notation -/

theorem saddle_Psi1Z : Psi1Z x₀ = 3 * π * I := by
  rw [Psi1Z_eq]; have := x₀_spec.2; rw [g_apply] at this; exact sub_eq_zero.1 this

theorem saddle_Psi2Z_dir : Psi2Z x₀ * dir ^ 2 = -(Kx : ℂ) := by
  rw [Psi2Z_eq]; exact dir_sq

theorem Psi3Z_bound {z : ℂ} (hz : z ∈ closedBall x₀ (ρ : ℝ)) : ‖Psi3Z z‖ ≤ (Mcert : ℝ) := by
  rw [Psi3Z_eq]; exact Z7_M_bound hz

theorem rho_M_Kx : (Mcert : ℝ) * ρ ≤ 3 * Kx / 2 := Z7_rho_M

theorem phase_saddle : phaseZ x₀ = Ω := by rw [phaseZ_eq]; rfl

theorem sector_disc {z : ℂ} (hz : z ∈ closedBall x₀ (ρ : ℝ)) :
    SectorAt (1 / 100) (π - 276 / 100) z :=
  sectorAt_of (S4_disc z hz)

/-! ## (S2), (S4) along the contour in `Z7/Analytic/` notation -/

end ZetaIrr.Z7.Interval
