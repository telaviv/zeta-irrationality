/-
# The top ray of the Z7 contour: (S3) and (S4) (PROOF_ZETA §6.3)

The contour ends with the vertical ray `X0 + i y`, `y ≥ Im xtop ≈ 12.0012`, `X0 = Re xtop ≈ 2.0512`.

* **(S3)** `S3_ray`: `Im Ψ'(X0 + i y) ≥ q0 = 12` for all `y ≥ Im xtop`: box checks on
  `[12.0012, 20]`, `[20, 40]` (`chk_ray`), and beyond `40` the analytic tail
  `Im Ψ' ≥ (π/2) Σ c - Σ |c| |s X0 + κ| / y = 5π - 142.86…/y` (`im_dpsiL_ge_tail`, `Σ c = 10`).
  Hence `∂h/∂y = 3π - Im Ψ' ≤ -(q0 - 3π) < -2.5` (`S3_h_decreasing`, `q0_sub_three_pi`).
* **(S4)** `S4_ray`: `|α_i| ≥ 12 ≥ 1/100` and `|arg α_i| ≤ π/2 + 1/3 ≤ 2.76` on the ray;
  `S4_ray_efactor`: `Re(2z + 1) > 0`.

All numerical checks are `decide +kernel` (no `native_decide`).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Interval.PolyDataZ7

namespace ZetaIrr.Z7.Interval

open Complex Metric ZetaIrr.Interval ZetaIrr.Interval.IV Real

def X0 : ℚ := xtop.1
def q0 : ℚ := 12
def rayYs : List ℚ := [20, 40]

lemma chk_ray : rayPts 40 16 facZ7 X0 q0 (xtop.2 :: rayYs) = true := by decide +kernel

lemma chk_tail : q0 ≤ 5 * (314 / 100) - tailB X0 facZ7 / 40 := by decide +kernel

lemma chk_tail0 : (0 : ℚ) ≤ tailB X0 facZ7 := by decide +kernel

lemma csum_facZ7 : csum facZ7 = 10 := by decide +kernel

/-- **(S3)** `Im Ψ' ≥ q0` on the whole top ray `Re z = X0`, `Im z ≥ Im xtop`. -/
theorem S3_ray (y : ℝ) (hy : (xtop.2 : ℝ) ≤ y) : (q0 : ℝ) ≤ (dpsiL facZ7 ⟨X0, y⟩).im := by
  rcases le_total y ((40 : ℚ) : ℝ) with h | h
  · exact ray_pts 40 16 facZ7 X0 q0 xtop.2 _ _ chk_ray y hy (by simpa [rayYs] using h)
  · have hY0 : (0 : ℝ) < ((40 : ℚ) : ℝ) := by norm_num
    have hy0 : (0 : ℝ) < y := hY0.trans_le h
    have ht := im_dpsiL_ge_tail facZ7 facZ7_s1 X0 (z := ⟨X0, y⟩) rfl hy0
    rw [csum_facZ7] at ht
    have hpi := Real.pi_gt_d2
    have hT : (0 : ℝ) ≤ (tailB X0 facZ7 : ℝ) := by exact_mod_cast chk_tail0
    have hdiv : (tailB X0 facZ7 : ℝ) / y ≤ (tailB X0 facZ7 : ℝ) / ((40 : ℚ) : ℝ) :=
      div_le_div_of_nonneg_left hT hY0 h
    have hc : (q0 : ℝ) ≤ ((5 * (314 / 100) - tailB X0 facZ7 / 40 : ℚ) : ℝ) := by
      exact_mod_cast chk_tail
    push_cast at hc ht hdiv ⊢
    linarith

lemma ray_eq (y : ℝ) : ((X0 : ℝ) : ℂ) + (y : ℂ) * I = ⟨X0, y⟩ := by
  apply Complex.ext <;> simp

lemma xtop2_pos : (0 : ℝ) < (xtop.2 : ℝ) := by simp [xtop]

lemma ray_good (y : ℝ) (hy : (xtop.2 : ℝ) ≤ y) : Good facZ7 (((X0 : ℝ) : ℂ) + (y : ℂ) * I) := by
  apply good_of_im
  rw [ray_eq]
  have := xtop2_pos
  simp only [ne_eq]
  intro h; change y = 0 at h; linarith

/-- `h` decreases along the top ray at rate `q0 - 3π > 2.5`. -/
theorem S3_h_decreasing {y1 y2 : ℝ} (h1 : (xtop.2 : ℝ) ≤ y1) (h12 : y1 ≤ y2) :
    (f ⟨X0, y2⟩).re ≤ (f ⟨X0, y1⟩).re - (q0 - 3 * π) * (y2 - y1) := by
  have := ray_h_decreasing 3 facZ7 X0 xtop.2 (q0 - 3 * π) (fun y hy => ray_good y hy)
    (fun y hy => by rw [ray_eq]; push_cast; linarith [S3_ray y hy]) h1 h12
  rw [ray_eq, ray_eq] at this
  exact this

theorem q0_sub_three_pi : (5 / 2 : ℝ) < q0 - 3 * π := by
  have := Real.pi_lt_d2; norm_num [q0]; linarith

lemma re_bound : ∀ b ∈ facZ7, |(b.s : ℚ) * X0 + b.κ| ≤ 4 := by decide +kernel

/-- **(S4) on the ray.** -/
theorem S4_ray (y : ℝ) (hy : (xtop.2 : ℝ) ≤ y) :
    ∀ a ∈ facZ7, (amin : ℝ) ≤ ‖a.α ⟨X0, y⟩‖ ∧ |arg (a.α ⟨X0, y⟩)| ≤ Amax := by
  intro a ha
  have hy60 : (12 : ℝ) ≤ y := le_trans (by simp [xtop]; norm_num) hy
  have hs := facZ7_s1 a ha
  have hre : |(a.α ⟨X0, y⟩).re| ≤ 4 := by
    have := re_bound a ha
    have e : (a.α ⟨X0, y⟩).re = (((a.s : ℚ) * X0 + a.κ : ℚ) : ℝ) := by simp [Fac.α]
    rw [e]; exact_mod_cast this
  have him : |(a.α ⟨X0, y⟩).im| = y := by
    rcases hs with h | h <;> simp [Fac.α, h, abs_of_pos (by linarith : (0 : ℝ) < y)]
  constructor
  · calc ((amin : ℚ) : ℝ) ≤ 12 := by norm_num
      _ ≤ |(a.α ⟨X0, y⟩).im| := by rw [him]; exact hy60
      _ ≤ ‖a.α ⟨X0, y⟩‖ := Complex.abs_im_le_norm _
  · have hat : |Real.arctan ((a.α ⟨X0, y⟩).re / (a.α ⟨X0, y⟩).im)| ≤ 4 / 12 := by
      refine Real.abs_arctan_le_abs.trans ?_
      rw [abs_div, him, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [abs_nonneg (a.α ⟨X0, y⟩).re]
    have hpi := Real.pi_lt_d2
    have hpi' := Real.pi_gt_three
    rcases hs with h | h
    · have hp : 0 < (a.α ⟨X0, y⟩).im := by simp [Fac.α, h]; linarith
      rw [arg_eq_of_im_pos hp]
      rw [abs_le] at hat ⊢
      constructor <;> norm_num [Amax] <;> linarith [hat.1, hat.2]
    · have hn : (a.α ⟨X0, y⟩).im < 0 := by simp [Fac.α, h]; linarith
      rw [arg_eq_of_im_neg hn]
      rw [abs_le] at hat ⊢
      constructor <;> norm_num [Amax] <;> linarith [hat.1, hat.2]

theorem S4_ray_efactor (y : ℝ) : 0 < (2 * (⟨X0, y⟩ : ℂ) + 1).re := by
  simp [X0, xtop]; norm_num

end ZetaIrr.Z7.Interval
