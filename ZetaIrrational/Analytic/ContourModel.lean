/-
# Ingredients for the contour formula

* `norm_sin_sq`: `‖sin z‖² = sin²(Re z) + sinh²(Im z)`, and its lower bounds.
* The *model kernel* `m_{t,s}(z) = (z - t)⁻¹ - (z - s)⁻¹` (real `t, s`), which has a simple pole
  of residue `1` at `t` and decays like `|z|⁻²`. On a vertical line `Re z = c` avoiding `t` and `s`:

      ∫_ℝ m_{t,s}(c + iy) dy = π (sgn(c - t) - sgn(c - s)),

  so `-2π` if `s < c < t`, and `0` if `s, t < c` (`integral_model_line`).
* `integrable_of_bound_inv_one_add_sq`: a continuous `g : ℝ → ℂ` with `‖g y‖ ≤ C (1 + y²)⁻¹`
  is integrable.
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace ZetaIrr.Analytic

open Complex Real MeasureTheory Set Filter Topology

/-- `‖sin z‖² = sin²(Re z) + sinh²(Im z)`. -/
lemma norm_sin_sq (z : ℂ) :
    ‖Complex.sin z‖ ^ 2 = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have e : Complex.sin z = ((Real.sin z.re * Real.cosh z.im : ℝ) : ℂ)
      + ((Real.cos z.re * Real.sinh z.im : ℝ) : ℂ) * I := by
    rw [Complex.sin_eq]; push_cast; ring
  rw [Complex.sq_norm, Complex.normSq_apply, e]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h1 := Real.cosh_sq z.im
  have h2 := Real.sin_sq_add_cos_sq z.re
  linear_combination (Real.sin z.re ^ 2) * h1 + (Real.sinh z.im ^ 2) * h2

lemma abs_sin_re_le_norm_sin (z : ℂ) : |Real.sin z.re| ≤ ‖Complex.sin z‖ := by
  have h : Real.sin z.re ^ 2 ≤ ‖Complex.sin z‖ ^ 2 := by
    rw [norm_sin_sq]; nlinarith [sq_nonneg (Real.sinh z.im)]
  exact abs_le.2 (abs_le_of_sq_le_sq' h (norm_nonneg _))

lemma abs_sinh_im_le_norm_sin (z : ℂ) : |Real.sinh z.im| ≤ ‖Complex.sin z‖ := by
  have h : Real.sinh z.im ^ 2 ≤ ‖Complex.sin z‖ ^ 2 := by
    rw [norm_sin_sq]; nlinarith [sq_nonneg (Real.sin z.re)]
  exact abs_le.2 (abs_le_of_sq_le_sq' h (norm_nonneg _))

/-- `sin (π z) ≠ 0` when `Re z` is not an integer. -/
lemma sin_pi_ne_zero_of_re {z : ℂ} (hz : ∀ k : ℤ, z.re ≠ k) : Complex.sin (π * z) ≠ 0 := by
  intro h0
  have h := abs_sin_re_le_norm_sin (π * z)
  rw [h0, norm_zero] at h
  have hs : Real.sin (π * z).re = 0 := abs_nonpos_iff.1 h
  have hre : (π * z : ℂ).re = π * z.re := by simp
  rw [hre, Real.sin_eq_zero_iff] at hs
  obtain ⟨k, hk⟩ := hs
  exact hz k (mul_right_cancel₀ Real.pi_ne_zero (by rw [hk]; ring : (k : ℝ) * π = z.re * π)).symm

/-- `sin (π z) ≠ 0` when `Im z ≠ 0`. -/
lemma sin_pi_ne_zero_of_im {z : ℂ} (hz : z.im ≠ 0) : Complex.sin (π * z) ≠ 0 := by
  intro h0
  have h := abs_sinh_im_le_norm_sin (π * z)
  rw [h0, norm_zero] at h
  have hs : Real.sinh (π * z).im = 0 := abs_nonpos_iff.1 h
  have him : (π * z : ℂ).im = π * z.im := by simp
  rw [him, Real.sinh_eq_zero] at hs
  exact hz (by
    rcases mul_eq_zero.1 hs with h1 | h1
    · exact absurd h1 Real.pi_ne_zero
    · exact h1)

/-! ### The Poisson kernel integral -/

lemma integrable_poisson (a : ℝ) (ha : a ≠ 0) :
    Integrable (fun y : ℝ => a / (a ^ 2 + y ^ 2)) := by
  have h := (integrable_inv_one_add_sq.comp_div ha).const_mul a⁻¹
  have e : (fun y : ℝ => a / (a ^ 2 + y ^ 2)) = fun y => a⁻¹ * (1 + (y / a) ^ 2)⁻¹ := by
    funext y; field_simp
  rw [e]; exact h

/-- `∫ a/(a² + y²) dy = π` for `a > 0`. -/
lemma integral_poisson_pos (a : ℝ) (ha : 0 < a) : ∫ y : ℝ, a / (a ^ 2 + y ^ 2) = π := by
  have h : (fun y : ℝ => a / (a ^ 2 + y ^ 2)) = fun y => a⁻¹ * (1 + (y / a) ^ 2)⁻¹ := by
    funext y; field_simp
  rw [h, integral_const_mul, Measure.integral_comp_div (fun y => (1 + y ^ 2)⁻¹) a,
    integral_univ_inv_one_add_sq, abs_of_pos ha, smul_eq_mul]
  field_simp

/-- `∫ a/(a² + y²) dy = -π` for `a < 0`. -/
lemma integral_poisson_neg (a : ℝ) (ha : a < 0) : ∫ y : ℝ, a / (a ^ 2 + y ^ 2) = -π := by
  have h := integral_poisson_pos (-a) (by linarith)
  have e : (fun y : ℝ => a / (a ^ 2 + y ^ 2)) = fun y => -((-a) / ((-a) ^ 2 + y ^ 2)) := by
    funext y; ring
  rw [e, integral_neg, h]

/-- The sign function `π · sgn a` used in the model integral. -/
noncomputable def piSgn (a : ℝ) : ℝ := if 0 < a then π else -π

lemma integral_poisson (a : ℝ) (ha : a ≠ 0) : ∫ y : ℝ, a / (a ^ 2 + y ^ 2) = piSgn a := by
  unfold piSgn
  split_ifs with h
  · exact integral_poisson_pos a h
  · exact integral_poisson_neg a (lt_of_le_of_ne (not_lt.1 h) ha)

/-- `∫ (a² + y²)⁻¹ dy = π / a` for `a > 0`. -/
lemma integral_inv_sq_add_sq (a : ℝ) (ha : 0 < a) : ∫ y : ℝ, (a ^ 2 + y ^ 2)⁻¹ = π / a := by
  have h := integral_poisson_pos a ha
  have e : (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) = fun y => a⁻¹ * (a / (a ^ 2 + y ^ 2)) := by
    funext y; field_simp
  rw [e, integral_const_mul, h]
  field_simp

lemma integrable_inv_sq_add_sq (a : ℝ) (ha : a ≠ 0) :
    Integrable (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) := by
  have h := (integrable_poisson a ha).const_mul a⁻¹
  have e : (fun y : ℝ => (a ^ 2 + y ^ 2)⁻¹) = fun y => a⁻¹ * (a / (a ^ 2 + y ^ 2)) := by
    funext y; field_simp
  rw [e]; exact h

/-- `|y| / (a² + y²) ≤ 1/(2|a|)`. -/
lemma abs_div_sq_add_sq_le (a y : ℝ) (ha : a ≠ 0) : |y| / (a ^ 2 + y ^ 2) ≤ 1 / (2 * |a|) := by
  have ha' : 0 < |a| := abs_pos.2 ha
  have hpos : 0 < a ^ 2 + y ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  have : (|a| - |y|) ^ 2 ≥ 0 := sq_nonneg _
  have h1 : |a| ^ 2 = a ^ 2 := sq_abs a
  have h2 : |y| ^ 2 = y ^ 2 := sq_abs y
  nlinarith

/-- The odd part `y/(a²+y²) - y/(b²+y²)` is integrable. -/
lemma integrable_odd_part (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun y : ℝ => y / (a ^ 2 + y ^ 2) - y / (b ^ 2 + y ^ 2)) := by
  have hdom : Integrable (fun y : ℝ => |b ^ 2 - a ^ 2| / (2 * |a|) * (b ^ 2 + y ^ 2)⁻¹) :=
    (integrable_inv_sq_add_sq b hb).const_mul _
  refine hdom.mono' (by fun_prop) (Eventually.of_forall fun y => ?_)
  have hpa : 0 < a ^ 2 + y ^ 2 := by positivity
  have hpb : 0 < b ^ 2 + y ^ 2 := by positivity
  have e : y / (a ^ 2 + y ^ 2) - y / (b ^ 2 + y ^ 2)
      = (b ^ 2 - a ^ 2) * (y / (a ^ 2 + y ^ 2)) * (b ^ 2 + y ^ 2)⁻¹ := by
    field_simp; ring
  rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_inv, abs_of_pos hpb, abs_div, abs_of_pos hpa]
  gcongr
  calc |b ^ 2 - a ^ 2| * (|y| / (a ^ 2 + y ^ 2)) ≤ |b ^ 2 - a ^ 2| * (1 / (2 * |a|)) :=
        mul_le_mul_of_nonneg_left (abs_div_sq_add_sq_le a y ha) (abs_nonneg _)
    _ = |b ^ 2 - a ^ 2| / (2 * |a|) := by ring

/-! ### The model kernel on a vertical line -/

/-- `(c + iy - t)⁻¹` in real and imaginary parts. -/
lemma inv_line_eq (c t y : ℝ) (h : c ≠ t) :
    ((c : ℂ) + y * I - t)⁻¹ =
      (((c - t) / ((c - t) ^ 2 + y ^ 2) : ℝ) : ℂ) - ((y / ((c - t) ^ 2 + y ^ 2) : ℝ) : ℂ) * I := by
  have hne : (c : ℂ) + y * I - t ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    exact h (by linarith)
  have hpos : 0 < (c - t) ^ 2 + y ^ 2 := by
    have : 0 < (c - t) ^ 2 := by
      have : c - t ≠ 0 := sub_ne_zero.2 h
      positivity
    positivity
  have hD : (((c - t) ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  apply inv_eq_of_mul_eq_one_right
  rw [show (((c - t) / ((c - t) ^ 2 + y ^ 2) : ℝ) : ℂ)
      = ((c - t : ℝ) : ℂ) / (((c - t) ^ 2 + y ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show ((y / ((c - t) ^ 2 + y ^ 2) : ℝ) : ℂ) = (y : ℂ) / (((c - t) ^ 2 + y ^ 2 : ℝ) : ℂ) by
      push_cast; ring]
  field_simp
  push_cast
  linear_combination (-(y : ℂ) ^ 2) * Complex.I_sq

/-- The model kernel `m_{t,s}(z) = (z - t)⁻¹ - (z - s)⁻¹`. -/
noncomputable def model (t s : ℝ) (z : ℂ) : ℂ := (z - t)⁻¹ - (z - s)⁻¹

lemma model_line_eq (c t s y : ℝ) (ht : c ≠ t) (hs : c ≠ s) :
    model t s ((c : ℂ) + y * I) =
      ((((c - t) / ((c - t) ^ 2 + y ^ 2)) - ((c - s) / ((c - s) ^ 2 + y ^ 2)) : ℝ) : ℂ)
      - (((y / ((c - t) ^ 2 + y ^ 2)) - (y / ((c - s) ^ 2 + y ^ 2)) : ℝ) : ℂ) * I := by
  unfold model
  rw [inv_line_eq c t y ht, inv_line_eq c s y hs]
  push_cast; ring

lemma integrable_model_line (c t s : ℝ) (ht : c ≠ t) (hs : c ≠ s) :
    Integrable (fun y : ℝ => model t s ((c : ℂ) + y * I)) := by
  have hat : c - t ≠ 0 := sub_ne_zero.2 ht
  have has : c - s ≠ 0 := sub_ne_zero.2 hs
  have h1 : Integrable (fun y : ℝ =>
      (((c - t) / ((c - t) ^ 2 + y ^ 2) - (c - s) / ((c - s) ^ 2 + y ^ 2) : ℝ) : ℂ)) :=
    ((integrable_poisson _ hat).sub (integrable_poisson _ has)).ofReal
  have h2 : Integrable (fun y : ℝ =>
      ((y / ((c - t) ^ 2 + y ^ 2) - y / ((c - s) ^ 2 + y ^ 2) : ℝ) : ℂ) * I) :=
    (integrable_odd_part _ _ hat has).ofReal.mul_const I
  exact (h1.sub h2).congr (Eventually.of_forall fun y => (model_line_eq c t s y ht hs).symm)

/-- An odd integrable function has integral `0`. -/
lemma integral_odd_eq_zero {g : ℝ → ℝ} (hg : ∀ y, g (-y) = -g y) : ∫ y, g y = 0 := by
  have h : ∫ y, g y = -∫ y, g y := by
    calc ∫ y, g y = ∫ y, g (-y) := (integral_neg_eq_self g volume).symm
      _ = ∫ y, -g y := by simp_rw [hg]
      _ = -∫ y, g y := integral_neg _
  linarith

/-- **Model integral.** `∫_ℝ m_{t,s}(c + iy) dy = π sgn(c - t) - π sgn(c - s)`. -/
lemma integral_model_line (c t s : ℝ) (ht : c ≠ t) (hs : c ≠ s) :
    ∫ y : ℝ, model t s ((c : ℂ) + y * I) = ((piSgn (c - t) - piSgn (c - s) : ℝ) : ℂ) := by
  have hat : c - t ≠ 0 := sub_ne_zero.2 ht
  have has : c - s ≠ 0 := sub_ne_zero.2 hs
  simp_rw [model_line_eq c t s _ ht hs]
  have h1 : Integrable (fun y : ℝ =>
      (((c - t) / ((c - t) ^ 2 + y ^ 2) - (c - s) / ((c - s) ^ 2 + y ^ 2) : ℝ) : ℂ)) :=
    ((integrable_poisson _ hat).sub (integrable_poisson _ has)).ofReal
  have h2 : Integrable (fun y : ℝ =>
      ((y / ((c - t) ^ 2 + y ^ 2) - y / ((c - s) ^ 2 + y ^ 2) : ℝ) : ℂ) * I) :=
    (integrable_odd_part _ _ hat has).ofReal.mul_const I
  rw [integral_sub h1 h2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
    integral_sub (integrable_poisson _ hat) (integrable_poisson _ has),
    integral_poisson _ hat, integral_poisson _ has,
    integral_odd_eq_zero (fun y => by ring)]
  simp

/-- `∫_ℝ m_{t,s}(c + iy) dy = -2π` if `s < c < t`. -/
lemma integral_model_line_of_lt (c t s : ℝ) (hct : c < t) (hsc : s < c) :
    ∫ y : ℝ, model t s ((c : ℂ) + y * I) = -2 * π := by
  rw [integral_model_line c t s hct.ne hsc.ne']
  unfold piSgn
  simp only [show ¬ (0 < c - t) by linarith, show 0 < c - s by linarith, ite_true, ite_false]
  push_cast; ring

/-- `∫_ℝ m_{t,s}(c + iy) dy = 0` if `t, s < c`. -/
lemma integral_model_line_of_gt (c t s : ℝ) (htc : t < c) (hsc : s < c) :
    ∫ y : ℝ, model t s ((c : ℂ) + y * I) = 0 := by
  rw [integral_model_line c t s htc.ne' hsc.ne']
  unfold piSgn
  simp only [show 0 < c - t by linarith, show 0 < c - s by linarith, ite_true]
  simp

/-! ### Integrability on lines from a pointwise bound -/

/-- A continuous `g : ℝ → ℂ` with `‖g y‖ ≤ C (1 + y²)⁻¹` is integrable. -/
lemma integrable_of_bound_inv_one_add_sq {g : ℝ → ℂ} {C : ℝ} (hg : Continuous g)
    (hb : ∀ y, ‖g y‖ ≤ C * (1 + y ^ 2)⁻¹) : Integrable g :=
  (integrable_inv_one_add_sq.const_mul C).mono' hg.aestronglyMeasurable
    (Eventually.of_forall hb)

end ZetaIrr.Analytic
