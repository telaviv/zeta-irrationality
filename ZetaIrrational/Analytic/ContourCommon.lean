/-
# Helpers for the contour formula

Elementary facts used by the contour formula `hasSum_cot_eq_line_integral` (`ContourCot.lean`):
* `sin_pi_ne_zero_of_ne_nat`: `sin(πz) ≠ 0` for `Re z > -1` off the natural numbers;
* `C_nonneg`, `inv_one_add_norm_sq_le`, `continuous_line`, `summable_inv_one_add_sq_nat`: decay and
  integrability bookkeeping for integrands bounded by `C (1 + ‖z‖²)⁻¹` on a vertical line;
* `poleSet`, `differentiableAt_model`, `continuousAt_model`: the integers `c < t ≤ N` whose principal
  parts are subtracted, and regularity of the model kernel `m_{t,s}(z) = (z - t)⁻¹ - (z - s)⁻¹`;
* `half_ne_int`: `N + 1/2` is not an integer;
* `integral_eq_two_re_Ioi`: for `g(-y) = conj g(y)`, `∫_ℝ g = 2 Re ∫_0^∞ g`.
-/
import ZetaIrrational.Analytic.ContourModel
import ZetaIrrational.Analytic.Removable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.PSeries

set_option autoImplicit false

namespace ZetaIrr.Analytic

open Complex Real MeasureTheory Set Filter Topology Metric

/-- `sin(π z) ≠ 0` for `Re z > -1` unless `z` is a natural number. -/
lemma sin_pi_ne_zero_of_ne_nat {z : ℂ} (hre : -1 < z.re) (hz : ∀ u : ℕ, z ≠ u) :
    Complex.sin (π * z) ≠ 0 := by
  by_cases him : z.im = 0
  · refine sin_pi_ne_zero_of_re (fun k hk => ?_)
    have hk0 : 0 ≤ k := by
      have : (-1 : ℝ) < k := hk ▸ hre
      exact_mod_cast (show (-1 : ℤ) < k by exact_mod_cast this)
    obtain ⟨u, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    exact hz u (Complex.ext (by simpa using hk) (by simpa using him))
  · exact sin_pi_ne_zero_of_im him

/-! ### The main identity for fixed `N` -/

section Identity

variable {f : ℂ → ℂ} {c₀ c C : ℝ}

lemma C_nonneg (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) : 0 ≤ C := by
  have h := (norm_nonneg _).trans (hb (c : ℂ) (by simp))
  exact nonneg_of_mul_nonneg_left h (inv_pos.2 (by positivity))

lemma inv_one_add_norm_sq_le (x y : ℝ) : (1 + ‖(x : ℂ) + y * I‖ ^ 2)⁻¹ ≤ (1 + y ^ 2)⁻¹ := by
  apply inv_anti₀ (by positivity)
  have h := Complex.abs_im_le_norm ((x : ℂ) + y * I)
  have him : ((x : ℂ) + y * I).im = y := by simp
  rw [him] at h
  have : y ^ 2 ≤ ‖(x : ℂ) + y * I‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith

lemma continuous_line (x : ℝ) : Continuous (fun y : ℝ => (x : ℂ) + y * I) := by fun_prop

/-- The finite set of poles `S_N = {t ∈ ℕ : c < t ≤ N}`. -/
noncomputable def poleSet (c : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun t => c < (t : ℝ))

lemma differentiableAt_model {t s : ℝ} {z : ℂ} (ht : z ≠ t) (hs : z ≠ s) :
    DifferentiableAt ℂ (model t s) z := by
  unfold model
  exact ((differentiableAt_id.sub_const (t : ℂ)).inv (sub_ne_zero.2 ht)).sub
    ((differentiableAt_id.sub_const (s : ℂ)).inv (sub_ne_zero.2 hs))

lemma continuousAt_model {t s : ℝ} {z : ℂ} (ht : z ≠ t) (hs : z ≠ s) :
    ContinuousAt (model t s) z := (differentiableAt_model ht hs).continuousAt

/-- `N + 1/2` is not an integer. -/
lemma half_ne_int (N : ℕ) (k : ℤ) : ((N : ℝ) + 1 / 2 : ℝ) ≠ k := by
  intro h
  have h2 : (2 * (N : ℤ) + 1 : ℝ) = 2 * k := by push_cast; linarith
  have h3 : 2 * (N : ℤ) + 1 = 2 * k := by exact_mod_cast h2
  omega

lemma summable_inv_one_add_sq_nat : Summable (fun t : ℕ => (1 + (t : ℝ) ^ 2)⁻¹) := by
  have hs2 : Summable (fun t : ℕ => (((t : ℝ) + 1) ^ 2)⁻¹) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
    simpa using this
  refine (hs2.mul_left 2).of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
  rw [show (2 : ℝ) * (((t : ℝ) + 1) ^ 2)⁻¹ = ((((t : ℝ) + 1) ^ 2) / 2)⁻¹ by field_simp]
  exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg ((t : ℝ) - 1)])

/-- For `g(-y) = conj g(y)`, `∫_ℝ g = 2 Re ∫_0^∞ g`. -/
lemma integral_eq_two_re_Ioi {g : ℝ → ℂ} (hg : Integrable g)
    (hsym : ∀ y, g (-y) = (starRingEnd ℂ) (g y)) :
    ∫ y, g y = ((2 * (∫ y in Ioi (0 : ℝ), g y).re : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hg.integrableOn hg.integrableOn]
  have h1 : ∫ y in Iic (0 : ℝ), g y = ∫ y in Iic (0 : ℝ), (starRingEnd ℂ) (g (-y)) := by
    congr 1; funext y; rw [hsym, Complex.conj_conj]
  rw [h1, integral_comp_neg_Iic 0 (fun y => (starRingEnd ℂ) (g y)), neg_zero, integral_conj,
    add_comm, Complex.add_conj]

end Identity

end ZetaIrr.Analytic
