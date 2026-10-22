/-
# The saddle value `Ω = f(x₀)` and `sin(240 Im Ω)` for instance Z7

With `x₀` the certified saddle of `SaddleZ7.lean` and `Ω = f(x₀) = Ψ(x₀) - 3πi x₀`:
* `Z7_ReOmega_le : Re Ω ≤ -10.1167485`, `Z7_ReOmega_ge : -10.1167486 ≤ Re Ω`;
* `mem_ImΩI`: an enclosure `Im Ω ∈ [-7.704987202, -7.704987200]` (up to outward rounding);
* `Z7_sinqtheta_le : sin(240 Im Ω) < -9/10` (`sin(240 Im Ω) ≈ -0.932453`).

Method: a box evaluation of `f(c0)` at the rational centre (precision `2^{-80}`, 40 series terms),
widened by the mean-value bound `‖f(x₀) - f(c0)‖ ≤ (10⁻¹⁶ + 30 R0) R0`. For the sine,
`240 Im Ω = (u - π/2) - 294 · 2π` with `|u| ≤ 0.38` (kernel check), so
`sin(240 Im Ω) = -cos u ≤ -(1 - u²/2)`.

All numerical checks are `decide +kernel` (no `native_decide`).
-/
import ZetaIrrational.Z7.Interval.SaddleZ7
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace ZetaIrr.Z7.Interval

open Complex Metric ZetaIrr.Interval ZetaIrr.Interval.IV Real

/-- **`Ω = f(x₀)`**, the saddle value. -/
noncomputable def Ω : ℂ := f x₀

def fP : CB := (psiB pp nn facZ7 P0).sub ((phIB 3).mul P0)

lemma mem_fP : fP.mem (f c0) :=
  CB.mem_sub (mem_psiB pp nn facZ7 mem_P0) (CB.mem_mul (mem_phIB 3) mem_P0)

/-- The radius by which `f c0`'s box is widened. -/
def wΩ : ℚ := (1 / 10 ^ 16 + 30 * R0) * R0

lemma norm_Ω_sub : ‖Ω - f c0‖ ≤ (wΩ : ℝ) := by
  have hmv := (convex_closedBall c0 (R0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := g) (C := ((1 / 10 ^ 16 + 30 * R0 : ℚ) : ℝ))
    (fun w hw => (Z7_hasDerivAt_f (im_ne_of_ball hw)).hasDerivWithinAt)
    (fun w hw => norm_g_le hw) c0_mem saddle_mem
  have hzc : ‖x₀ - c0‖ ≤ R0 := by rw [← dist_eq_norm]; exact saddle_mem
  have hC : (0 : ℝ) ≤ ((1 / 10 ^ 16 + 30 * R0 : ℚ) : ℝ) := by norm_num [R0]
  calc ‖Ω - f c0‖ ≤ ((1 / 10 ^ 16 + 30 * R0 : ℚ) : ℝ) * ‖x₀ - c0‖ := hmv
    _ ≤ ((1 / 10 ^ 16 + 30 * R0 : ℚ) : ℝ) * R0 := mul_le_mul_of_nonneg_left hzc hC
    _ = (wΩ : ℝ) := by simp [wΩ]

/-- Interval for `Re Ω`. -/
def ReΩI : IV := fP.re.widen wΩ
/-- Interval for `Im Ω`. -/
def ImΩI : IV := fP.im.widen wΩ

lemma mem_ReΩI : ReΩI.mem Ω.re := by
  refine mem_widen mem_fP.1 ?_
  rw [← sub_re]; exact (abs_re_le_norm _).trans norm_Ω_sub

lemma mem_ImΩI : ImΩI.mem Ω.im := by
  refine mem_widen mem_fP.2 ?_
  rw [← sub_im]; exact (abs_im_le_norm _).trans norm_Ω_sub

lemma chk_Re_hi : ReΩI.hiLe (-101167485 / 10 ^ 7) = true := by decide +kernel
lemma chk_Re_lo : ReΩI.loGe (-101167486 / 10 ^ 7) = true := by decide +kernel

/-- `Re Ω ≤ -10.1167485`. -/
theorem Z7_ReOmega_le : Ω.re ≤ -101167485 / 10 ^ 7 := by
  have := le_of_hiLe mem_ReΩI chk_Re_hi
  push_cast at this; exact this

theorem Z7_ReOmega_ge : -101167486 / 10 ^ 7 ≤ Ω.re := by
  have := ge_of_loGe mem_ReΩI chk_Re_lo
  push_cast at this; exact this

/-! ## `sin(240 Im Ω) < -0.9` -/

/-- `u = 240 Im Ω + (1177/2) π`, so that `240 Im Ω = (u - π/2) - 294 · 2π`. -/
def uH4 : IV := (ImΩI.smul 240).add (piI.smul (1177 / 2))

lemma mem_uH4 : uH4.mem (240 * Ω.im + 1177 / 2 * π) := by
  have := mem_add (mem_smul 240 mem_ImΩI) (mem_smul (1177 / 2) mem_piI)
  push_cast at this; exact this

lemma chk_u : uH4.absLe (38 / 100) = true := by decide +kernel

/-- `sin(q · Im Ω) < -0.9` with `q = 240`, so `sin(240 Im Ω) ≠ 0`. -/
theorem Z7_sinqtheta_le : Real.sin (240 * Ω.im) < -9 / 10 := by
  set u := 240 * Ω.im + 1177 / 2 * π with hu
  have hsin : Real.sin (240 * Ω.im) = -Real.cos u := by
    rw [← Real.sin_sub_pi_div_two, ← Real.sin_sub_nat_mul_two_pi (u - π / 2) 294]
    congr 1; rw [hu]; push_cast; ring
  rw [hsin]
  have h1 := abs_le_of_absLe mem_uH4 chk_u
  push_cast at h1
  have h2 := Real.one_sub_sq_div_two_le_cos (x := u)
  have h3 : u ^ 2 ≤ (38 / 100) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith

end ZetaIrr.Z7.Interval
