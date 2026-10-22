/-
# Stirling for a product of Γ-factors (PROOF_BETA100 §6.4 (6.4.1); PROOF_ZETA §6.4)

For a finite factor list `(c_i, α_i, β_i, s_i)` (`c_i ∈ ℤ`, `α_i ∈ ℂ` the value `α_i(x)` at the
current point, `β_i ∈ [0, 2]`, slope `s_i`), with the sector condition (S4)
`‖α_i‖ ≥ a`, `|arg α_i| ≤ π - φ`, and `n ≥ 4/a`:

* `prod_Gamma_zpow_eq_exp`: `Π Γ(nα_i + β_i)^{c_i} = exp(Σ c_i logΓ(nα_i + β_i))`;
* `norm_sum_logGamma_sub_main_le`:
  `‖Σ c_i (logΓ(nα_i + β_i) - main_i)‖ ≤ (Σ|c_i|) (9 + 1/(6 sin²(φ/2))) / (a n)`;
* `sum_main_eq`: `Σ c_i main_i = (Σ c_i α_i) n log n + n Σ c_i (α_i log α_i - α_i)
     + (Σ c_i (β_i - 1/2)) log n + Σ c_i (β_i - 1/2) log α_i + (Σ c_i / 2) log 2π`.
  With `Σ c_i α_i = -G` this is (6.4.1): `-G n log n + G n + nΨ(x) + κ' log n + ψ₀(x) + …`;

lean_zeta7 change: `β_i ∈ [0, 2]` (the ζ factor list has `β = 0`), and the digamma sums of
lean_beta (`Λ_n`, `Λ_n'`) are dropped: the ζ integrand `R_n k⁗` needs no logarithmic derivatives.

These use the uniform complex Stirling bounds of `ZetaIrrational/Stirling/`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Stirling.All

set_option autoImplicit false

namespace ZetaIrr.Analytic

open Complex Finset

/-- The Stirling main term `nα log n + n(α log α - α) + (β - 1/2)(log n + log α) + (1/2) log 2π`. -/
noncomputable def mainTerm (n : ℝ) (α : ℂ) (β : ℝ) : ℂ :=
  (n : ℂ) * α * (Real.log n : ℂ) + n * (α * Complex.log α - α) +
    (β - 1 / 2) * ((Real.log n : ℂ) + Complex.log α) + (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ)

variable {ι : Type*} (S : Finset ι) (c : ι → ℤ) (α : ι → ℂ) (β : ι → ℝ)

/-- The sector hypotheses (S4) for every factor, at one point. -/
def SectorHyp (φ a : ℝ) : Prop :=
  ∀ i ∈ S, a ≤ ‖α i‖ ∧ |Complex.arg (α i)| ≤ Real.pi - φ ∧ 0 ≤ β i ∧ β i ≤ 2

theorem prod_Gamma_zpow_eq_exp {φ a n : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi) (ha : 0 < a)
    (h : SectorHyp S α β φ a) (hn : 4 / a ≤ n) :
    ∏ i ∈ S, Complex.Gamma (n * α i + β i) ^ c i
      = Complex.exp (∑ i ∈ S, (c i : ℂ) * Stirling.logGammaS (n * α i + β i)) := by
  rw [Complex.exp_sum]
  refine prod_congr rfl (fun i hi => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := h i hi
  rw [(Stirling.stirling_scaled hφ0 hφ ha h1 h2 h3 h4 hn).1, Complex.exp_int_mul]

theorem norm_sum_logGamma_sub_main_le {φ a n : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi) (ha : 0 < a)
    (h : SectorHyp S α β φ a) (hn : 4 / a ≤ n) :
    ‖∑ i ∈ S, (c i : ℂ) * (Stirling.logGammaS (n * α i + β i) - mainTerm n (α i) (β i))‖
      ≤ (∑ i ∈ S, |(c i : ℝ)|) * ((9 + 1 / (6 * Real.sin (φ / 2) ^ 2)) / (a * n)) := by
  rw [sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum (fun i hi => ?_))
  obtain ⟨h1, h2, h3, h4⟩ := h i hi
  rw [norm_mul]
  have hc : ‖(c i : ℂ)‖ = |(c i : ℝ)| := by
    rw [show ((c i : ℤ) : ℂ) = (((c i : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs]
  rw [hc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have := (Stirling.stirling_scaled hφ0 hφ ha h1 h2 h3 h4 hn).2
  unfold mainTerm
  exact this

/-- The algebraic regrouping of the main terms. -/
theorem sum_main_eq (n : ℝ) :
    ∑ i ∈ S, (c i : ℂ) * mainTerm n (α i) (β i)
      = (∑ i ∈ S, (c i : ℂ) * α i) * n * (Real.log n : ℂ)
        + n * ∑ i ∈ S, (c i : ℂ) * (α i * Complex.log (α i) - α i)
        + (∑ i ∈ S, (c i : ℂ) * (β i - 1 / 2)) * (Real.log n : ℂ)
        + ∑ i ∈ S, (c i : ℂ) * (β i - 1 / 2) * Complex.log (α i)
        + (∑ i ∈ S, (c i : ℂ)) / 2 * (Real.log (2 * Real.pi) : ℂ) := by
  unfold mainTerm
  simp only [sum_mul, mul_sum, sum_div, ← sum_add_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  ring

end ZetaIrr.Analytic
