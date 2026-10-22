/-
# Scaled ψ and ψ′ (the expansions behind PROOF_BETA100 (6.4.3))

Hypotheses as in `stirling_scaled`: `0 < φ ≤ π`, `a > 0`, `‖α‖ ≥ a`, `|arg α| ≤ π - φ`,
real `β ∈ (0, 2]`, real `n ≥ 4/a`; `s = sin(φ/2)`.

* `digamma_scaled`: `‖ψ(nα + β) - (log n + log α)‖ ≤ (4 + 1/(8 s³)) / (a n)`;
* `deriv_digamma_scaled`: `‖ψ'(nα + β)‖ ≤ (3 + 1/s⁴) / (a n)`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Stirling.Scaled
import ZetaIrrational.Stirling.Digamma

namespace ZetaIrr.Stirling

open Complex Set Filter Topology

/-- Common setup for `w = nα + β` (see `stirling_scaled`). -/
lemma scaled_setup {φ a : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi) (ha : 0 < a) {α : ℂ}
    (hαa : a ≤ ‖α‖) (harg : |arg α| ≤ Real.pi - φ) {β : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 2) {n : ℝ}
    (hn : 4 / a ≤ n) :
    0 < n ∧ 4 ≤ a * n ∧ 0 < Real.sin (φ / 2) ∧
    SectorBound (Real.sin (φ / 2)) ((n : ℂ) * α + β) ∧
    a * n / 2 ≤ ‖(n : ℂ) * α + β‖ ∧ (n : ℂ) * α + β ≠ 0 ∧ (n : ℂ) * α + β ∈ slitPlane ∧
    ‖(β : ℂ) / (n * α)‖ ≤ 2 / (a * n) ∧ ‖(β : ℂ) / (n * α)‖ ≤ 1 / 2 ∧
    log ((n : ℂ) * α + β) = (Real.log n : ℂ) + (log α + log (1 + (β : ℂ) / (n * α))) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hX : 4 ≤ a * n := by rw [div_le_iff₀ ha] at hn; linarith
  have hα0 : α ≠ 0 := by intro h; rw [h, norm_zero] at hαa; linarith
  have hs : 0 < Real.sin (φ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hsα := sectorBound_of_arg hφ0 hφ harg
  have hsw : SectorBound (Real.sin (φ / 2)) ((n : ℂ) * α + β) :=
    (hsα.smul_pos hn0).add_pos hs.le hβ0.le
  have hnα : ‖(n : ℂ) * α‖ = n * ‖α‖ := by rw [norm_mul, Complex.norm_of_nonneg hn0.le]
  have hna : a * n ≤ n * ‖α‖ := by nlinarith
  have hw_big : a * n / 2 ≤ ‖(n : ℂ) * α + β‖ := by
    have h1 : ‖(n : ℂ) * α‖ ≤ ‖(n : ℂ) * α + β‖ + ‖(β : ℂ)‖ := by
      calc ‖(n : ℂ) * α‖ = ‖((n : ℂ) * α + β) - β‖ := by ring_nf
        _ ≤ ‖(n : ℂ) * α + β‖ + ‖(β : ℂ)‖ := norm_sub_le _ _
    rw [hnα, Complex.norm_of_nonneg hβ0.le] at h1
    linarith
  have hw0 : (n : ℂ) * α + β ≠ 0 := by
    intro h; rw [h, norm_zero] at hw_big; linarith
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  set u : ℂ := (β : ℂ) / (n * α) with hudef
  have hunorm : ‖u‖ = β / (n * ‖α‖) := by
    rw [hudef, norm_div, hnα, Complex.norm_of_nonneg hβ0.le]
  have hu2 : ‖u‖ ≤ 2 / (a * n) := by
    rw [hunorm]
    apply div_le_div₀ (by norm_num) hβ2 (by positivity) hna
  have hu12 : ‖u‖ ≤ 1 / 2 := by
    calc ‖u‖ ≤ 2 / (a * n) := hu2
      _ ≤ 2 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
      _ = 1 / 2 := by norm_num
  have hw_eq : (n : ℂ) * α + β = (n : ℂ) * (α * (1 + u)) := by
    rw [hudef]; field_simp
  have h1u : 1 + u ≠ 0 := by
    intro h
    have : ‖(1 : ℂ) + u‖ ≥ 1 / 2 := by
      have := norm_sub_norm_le (1 : ℂ) (-u)
      simp at this
      linarith
    rw [h, norm_zero] at this; linarith
  have hlogw : log ((n : ℂ) * α + β) = (Real.log n : ℂ) + (log α + log (1 + u)) := by
    rw [hw_eq, log_ofReal_mul hn0 (mul_ne_zero hα0 h1u)]
    rw [log_mul_one_add hα0 hβ0.le hn0 hu12]
  exact ⟨hn0, hX, hs, hsw, hw_big, hw0, hsw.mem_slitPlane hs hw0, hu2, hu12, hlogw⟩

/-- **Scaled ψ**: `‖ψ(nα + β) - (log n + log α)‖ ≤ (4 + 1/(8 sin³(φ/2))) / (a n)`. -/
theorem digamma_scaled {φ a : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi) (ha : 0 < a) {α : ℂ}
    (hαa : a ≤ ‖α‖) (harg : |arg α| ≤ Real.pi - φ) {β : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 2) {n : ℝ}
    (hn : 4 / a ≤ n) :
    ‖digamma ((n : ℂ) * α + β) - ((Real.log n : ℂ) + log α)‖ ≤
      (4 + 1 / (8 * Real.sin (φ / 2) ^ 3)) / (a * n) := by
  obtain ⟨hn0, hX, hs, hsw, hw_big, hw0, hwslit, hu2, hu12, hlogw⟩ :=
    scaled_setup hφ0 hφ ha hαa harg hβ0 hβ2 hn
  set s := Real.sin (φ / 2)
  set w : ℂ := (n : ℂ) * α + β with hwdef
  set u : ℂ := (β : ℂ) / (n * α)
  have hX0 : 0 < a * n := by linarith
  have hwpos : 0 < ‖w‖ := by linarith
  have hw2 : a * n ≤ ‖w‖ ^ 2 := by nlinarith
  rw [digamma_eq hwslit, hlogw]
  have e : (Real.log n : ℂ) + (log α + log (1 + u)) - 1 / (2 * w) - 2 * Jm 3 w -
      ((Real.log n : ℂ) + log α) = log (1 + u) - 1 / (2 * w) - 2 * Jm 3 w := by ring
  rw [e]
  have h1 : ‖log (1 + u)‖ ≤ 3 / (a * n) := by
    calc ‖log (1 + u)‖ ≤ 3 / 2 * ‖u‖ := norm_log_one_add_half_le_self hu12
      _ ≤ 3 / 2 * (2 / (a * n)) := by gcongr
      _ = 3 / (a * n) := by ring
  have h2 : ‖1 / (2 * w)‖ ≤ 1 / (a * n) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
    apply div_le_div_of_nonneg_left (by norm_num) hX0
    linarith
  have h3 : ‖2 * Jm 3 w‖ ≤ 1 / (8 * s ^ 3) / (a * n) := by
    rw [norm_mul, Complex.norm_ofNat]
    calc 2 * ‖Jm 3 w‖ ≤ 2 * (1 / (16 * s ^ 3 * ‖w‖ ^ 2)) := by
          gcongr; exact norm_Jm3_le hs hw0 hsw
      _ = 1 / (8 * s ^ 3 * ‖w‖ ^ 2) := by field_simp; ring
      _ ≤ 1 / (8 * s ^ 3 * (a * n)) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact mul_le_mul_of_nonneg_left hw2 (by positivity)
      _ = 1 / (8 * s ^ 3) / (a * n) := by field_simp
  calc ‖log (1 + u) - 1 / (2 * w) - 2 * Jm 3 w‖
      ≤ ‖log (1 + u)‖ + ‖1 / (2 * w)‖ + ‖2 * Jm 3 w‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ 3 / (a * n) + 1 / (a * n) + 1 / (8 * s ^ 3) / (a * n) := by linarith
    _ = (4 + 1 / (8 * s ^ 3)) / (a * n) := by field_simp; ring

/-- **Scaled ψ′**: `‖ψ'(nα + β)‖ ≤ (3 + 1/sin⁴(φ/2)) / (a n)`. -/
theorem deriv_digamma_scaled {φ a : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi) (ha : 0 < a) {α : ℂ}
    (hαa : a ≤ ‖α‖) (harg : |arg α| ≤ Real.pi - φ) {β : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 2) {n : ℝ}
    (hn : 4 / a ≤ n) :
    ‖deriv digamma ((n : ℂ) * α + β)‖ ≤ (3 + 1 / Real.sin (φ / 2) ^ 4) / (a * n) := by
  obtain ⟨hn0, hX, hs, hsw, hw_big, hw0, hwslit, -, -, -⟩ :=
    scaled_setup hφ0 hφ ha hαa harg hβ0 hβ2 hn
  set s := Real.sin (φ / 2)
  set w : ℂ := (n : ℂ) * α + β with hwdef
  have hX0 : 0 < a * n := by linarith
  have hwpos : 0 < ‖w‖ := by linarith
  have hw1 : 1 ≤ ‖w‖ := by linarith
  have hw2 : a * n ≤ ‖w‖ ^ 2 := by nlinarith
  have hw3 : a * n ≤ ‖w‖ ^ 3 := by
    calc a * n ≤ ‖w‖ ^ 2 := hw2
      _ = ‖w‖ ^ 2 * 1 := by ring
      _ ≤ ‖w‖ ^ 2 * ‖w‖ := by gcongr
      _ = ‖w‖ ^ 3 := by ring
  rw [(hasDerivAt_digamma hwslit).deriv]
  have h1 : ‖1 / w‖ ≤ 2 / (a * n) := by
    rw [norm_div, norm_one]
    rw [div_le_div_iff₀ hwpos hX0]; linarith
  have h2 : ‖1 / (2 * w ^ 2)‖ ≤ 1 / 2 / (a * n) := by
    rw [norm_div, norm_one, norm_mul, norm_pow, Complex.norm_ofNat]
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h3 : ‖6 * Jm 4 w‖ ≤ 1 / (4 * s ^ 4) / (a * n) := by
    rw [norm_mul, Complex.norm_ofNat]
    calc 6 * ‖Jm 4 w‖ ≤ 6 * (1 / (24 * s ^ 4 * ‖w‖ ^ 3)) := by
          gcongr; exact norm_Jm4_le hs hw0 hsw
      _ = 1 / (4 * s ^ 4 * ‖w‖ ^ 3) := by field_simp; ring
      _ ≤ 1 / (4 * s ^ 4 * (a * n)) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact mul_le_mul_of_nonneg_left hw3 (by positivity)
      _ = 1 / (4 * s ^ 4) / (a * n) := by field_simp
  have hs4 : 1 / (4 * s ^ 4) ≤ 1 / s ^ 4 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith [pow_pos hs 4])
  calc ‖1 / w + 1 / (2 * w ^ 2) + 6 * Jm 4 w‖
      ≤ ‖1 / w‖ + ‖1 / (2 * w ^ 2)‖ + ‖6 * Jm 4 w‖ := norm_add₃_le
    _ ≤ 2 / (a * n) + 1 / 2 / (a * n) + 1 / (4 * s ^ 4) / (a * n) := by linarith
    _ = (5 / 2 + 1 / (4 * s ^ 4)) / (a * n) := by field_simp; ring
    _ ≤ (3 + 1 / s ^ 4) / (a * n) := by
        apply div_le_div_of_nonneg_right _ hX0.le
        linarith

end ZetaIrr.Stirling
