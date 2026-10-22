/-
# Four integrations by parts on a vertical line (Lemma 6)

`integral_line_by_parts4`: let `g j`, `k j` (`j ≤ 4`) be chains of derivatives at every point of
the line `Re z = c` (`(g j)' = g (j+1)`, `(k j)' = k (j+1)`), with `g 4 · k 0` and `g 0 · k 4`
integrable on the line, `g j(c + iy) → 0` as `y → ±∞` for `j ≤ 3`, and `k j` bounded on the line
for `j ≤ 3`. Then

    ∫_ℝ g₄(c+iy) k₀(c+iy) dy = ∫_ℝ g₀(c+iy) k₄(c+iy) dy.

Proof: `W = g₃k₀ - g₂k₁ + g₁k₂ - g₀k₃` has `W' = g₄k₀ - g₀k₄` and tends to `0` at both ends, so the
fundamental theorem of calculus on `ℝ` (`integral_of_hasDerivAt_of_tendsto`) gives
`∫ (g₄k₀ - g₀k₄) = 0`.
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

namespace ZetaIrr.Analytic

open Complex Real MeasureTheory Filter Topology

lemma hasDerivAt_line (c y : ℝ) :
    HasDerivAt (fun y : ℝ => (c : ℂ) + (y : ℂ) * I) I y := by
  have h := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (c : ℂ)
  simpa using h

/-- **Four integrations by parts on the line `Re z = c`.** -/
theorem integral_line_by_parts4 (g k : ℕ → ℂ → ℂ) (c : ℝ)
    (hg : ∀ j < 4, ∀ y : ℝ, HasDerivAt (g j) (g (j + 1) (c + y * I)) (c + y * I))
    (hk : ∀ j < 4, ∀ y : ℝ, HasDerivAt (k j) (k (j + 1) (c + y * I)) (c + y * I))
    (hint1 : Integrable (fun y : ℝ => g 4 (c + y * I) * k 0 (c + y * I)))
    (hint2 : Integrable (fun y : ℝ => g 0 (c + y * I) * k 4 (c + y * I)))
    (hlimT : ∀ j < 4, Tendsto (fun y : ℝ => g j (c + y * I)) atTop (𝓝 0))
    (hlimB : ∀ j < 4, Tendsto (fun y : ℝ => g j (c + y * I)) atBot (𝓝 0))
    (B : ℝ) (hkB : ∀ j < 4, ∀ y : ℝ, ‖k j (c + y * I)‖ ≤ B) :
    ∫ y : ℝ, g 4 (c + y * I) * k 0 (c + y * I) = ∫ y : ℝ, g 0 (c + y * I) * k 4 (c + y * I) := by
  set p : ℝ → ℂ := fun y => (c : ℂ) + (y : ℂ) * I with hp
  set W : ℂ → ℂ := fun z => g 3 z * k 0 z - g 2 z * k 1 z + g 1 z * k 2 z - g 0 z * k 3 z
    with hW
  have hWd : ∀ y : ℝ, HasDerivAt W (g 4 (p y) * k 0 (p y) - g 0 (p y) * k 4 (p y)) (p y) := by
    intro y
    have h30 := (hg 3 (by norm_num) y).mul (hk 0 (by norm_num) y)
    have h21 := (hg 2 (by norm_num) y).mul (hk 1 (by norm_num) y)
    have h12 := (hg 1 (by norm_num) y).mul (hk 2 (by norm_num) y)
    have h03 := (hg 0 (by norm_num) y).mul (hk 3 (by norm_num) y)
    have := ((h30.sub h21).add h12).sub h03
    convert this using 1
    simp only [hp]
    ring
  have hφ : ∀ y : ℝ, HasDerivAt (fun y => W (p y))
      ((g 4 (p y) * k 0 (p y) - g 0 (p y) * k 4 (p y)) * I) y := fun y =>
    (hWd y).comp y (hasDerivAt_line c y)
  -- `W ∘ p → 0` at both ends
  have hprod : ∀ (F : Filter ℝ), (∀ j < 4, Tendsto (fun y : ℝ => g j (p y)) F (𝓝 0)) →
      Tendsto (fun y => W (p y)) F (𝓝 0) := by
    intro F hF
    have hterm : ∀ i j, i < 4 → j < 4 →
        Tendsto (fun y : ℝ => g i (p y) * k j (p y)) F (𝓝 0) := by
      intro i j hi hj
      refine squeeze_zero_norm (a := fun y => ‖g i (p y)‖ * B) (fun y => ?_) ?_
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hkB j hj y) (norm_nonneg _)
      · simpa using ((hF i hi).norm.mul_const B)
    have := (((hterm 3 0 (by norm_num) (by norm_num)).sub (hterm 2 1 (by norm_num)
      (by norm_num))).add (hterm 1 2 (by norm_num) (by norm_num))).sub
      (hterm 0 3 (by norm_num) (by norm_num))
    simpa [hW] using this
  have hint : Integrable (fun y : ℝ => (g 4 (p y) * k 0 (p y) - g 0 (p y) * k 4 (p y)) * I) :=
    (hint1.sub hint2).mul_const I
  have hFTC := integral_of_hasDerivAt_of_tendsto hφ hint (hprod atBot hlimB) (hprod atTop hlimT)
  rw [sub_zero, integral_mul_const] at hFTC
  have h0 : ∫ y : ℝ, (g 4 (p y) * k 0 (p y) - g 0 (p y) * k 4 (p y)) = 0 :=
    (mul_eq_zero.1 hFTC).resolve_right Complex.I_ne_zero
  rw [integral_sub hint1 hint2] at h0
  exact sub_eq_zero.1 h0

end ZetaIrr.Analytic
