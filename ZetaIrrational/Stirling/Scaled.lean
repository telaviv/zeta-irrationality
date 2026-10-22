/-
# The scaled Stirling expansion used in PROOF_BETA100 §6.4 ("Application")

`stirling_scaled`: for `0 < φ ≤ π`, `a > 0`, `α ∈ ℂ` with `‖α‖ ≥ a` and `|arg α| ≤ π - φ`,
real `β ∈ (0, 2]`, and real `n ≥ 4/a`:

    Γ(nα + β) = exp (logGammaS (nα + β)),
    ‖logGammaS (nα + β) - [nα log n + n(α log α - α) + (β - 1/2)(log n + log α) + (1/2) log 2π]‖
        ≤ (9 + 1/(6 sin²(φ/2))) / (a n).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Stirling.Bound

namespace ZetaIrr.Stirling

open Complex Set Filter Topology

lemma SectorBound.mem_slitPlane {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ≠ 0) (h : SectorBound s w) :
    w ∈ slitPlane := by
  by_contra hns
  rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hns
  have hne := h.ne_zero hs hw (t := -w.re) (by linarith [hns.1])
  apply hne
  apply Complex.ext <;> simp [hns.2]

/-- The branch splitting `log(α(1+u)) = log α + log(1+u)` for `u = β/(nα)`, `β, n > 0`, `‖u‖ ≤ 1/2`. -/
lemma log_mul_one_add {α : ℂ} (hα : α ≠ 0) {β n : ℝ} (hβ : 0 < β)
    (hn : 0 < n) (hu : ‖(β : ℂ) / (n * α)‖ ≤ 1 / 2) :
    log (α * (1 + (β : ℂ) / (n * α))) = log α + log (1 + (β : ℂ) / (n * α)) := by
  set u : ℂ := (β : ℂ) / (n * α) with hudef
  have hre : 0 < (1 + u).re := by
    have := Complex.abs_re_le_norm u
    simp only [add_re, one_re]
    have := abs_le.mp this |>.1
    linarith
  have h1u : 1 + u ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have habs : |arg (1 + u)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have habs' := abs_lt.mp habs
  have hnα : (n : ℂ) * α ≠ 0 := mul_ne_zero (by exact_mod_cast hn.ne') hα
  have hns : 0 < normSq ((n : ℂ) * α) := normSq_pos.mpr hnα
  have hui : (1 + u).im = -(β * (n * α.im)) / normSq ((n : ℂ) * α) := by
    simp only [add_im, one_im, zero_add, hudef, div_im, ofReal_re, ofReal_im, mul_im, zero_mul,
      ofReal_re, ofReal_im]
    ring
  rw [log_mul_eq_add_log_iff hα h1u, mem_Ioc]
  have hpi := Real.pi_pos
  rcases le_or_gt 0 α.im with him | him
  · -- arg α ∈ [0, π], arg (1+u) ∈ (-π/2, 0]
    have h0 : 0 ≤ arg α := arg_nonneg_iff.mpr him
    have h1 : arg (1 + u) ≤ 0 := by
      have hle : (1 + u).im ≤ 0 := by
        rw [hui]; apply div_nonpos_of_nonpos_of_nonneg _ hns.le
        have : 0 ≤ β * (n * α.im) := by positivity
        linarith
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact (arg_neg_iff.mpr hlt).le
      · exact (arg_eq_zero_iff.mpr ⟨hre.le, heq⟩).le
    exact ⟨by linarith, by linarith [arg_le_pi α]⟩
  · -- arg α ∈ (-π, 0), arg (1+u) ∈ [0, π/2)
    have h0 : arg α < 0 := arg_neg_iff.mpr him
    have h1 : 0 ≤ arg (1 + u) := by
      apply arg_nonneg_iff.mpr
      rw [hui]
      apply div_nonneg _ hns.le
      have : β * (n * α.im) < 0 := by
        apply mul_neg_of_pos_of_neg hβ (mul_neg_of_pos_of_neg hn him)
      linarith
    exact ⟨by linarith [neg_pi_lt_arg α], by linarith⟩

/-- **Scaled uniform Stirling** (PROOF_BETA100 §6.4, the form used downstream). -/
theorem stirling_scaled {φ a : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi) (ha : 0 < a) {α : ℂ}
    (hαa : a ≤ ‖α‖) (harg : |arg α| ≤ Real.pi - φ) {β : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 2) {n : ℝ}
    (hn : 4 / a ≤ n) :
    Gamma (n * α + β) = exp (logGammaS (n * α + β)) ∧
    ‖logGammaS (n * α + β) -
        ((n : ℂ) * α * (Real.log n : ℂ) + n * (α * log α - α) +
          (β - 1 / 2) * ((Real.log n : ℂ) + log α) + (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ))‖
      ≤ (9 + 1 / (6 * Real.sin (φ / 2) ^ 2)) / (a * n) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hX : 4 ≤ a * n := by rw [div_le_iff₀ ha] at hn; linarith
  have hα0 : α ≠ 0 := by intro h; rw [h, norm_zero] at hαa; linarith
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  have hs : 0 < Real.sin (φ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set s := Real.sin (φ / 2) with hsdef
  have hsα := sectorBound_of_arg hφ0 hφ harg
  set w : ℂ := n * α + β with hwdef
  have hsw : SectorBound s w := (hsα.smul_pos hn0).add_pos hs.le hβ0.le
  -- size of w
  have hnα : ‖(n : ℂ) * α‖ = n * ‖α‖ := by rw [norm_mul, Complex.norm_of_nonneg hn0.le]
  have hna : a * n ≤ n * ‖α‖ := by nlinarith
  have hw_big : a * n / 2 ≤ ‖w‖ := by
    have h1 : ‖(n : ℂ) * α‖ ≤ ‖w‖ + ‖(β : ℂ)‖ := by
      calc ‖(n : ℂ) * α‖ = ‖w - β‖ := by rw [hwdef]; ring_nf
        _ ≤ ‖w‖ + ‖(β : ℂ)‖ := norm_sub_le _ _
    rw [hnα, Complex.norm_of_nonneg hβ0.le] at h1
    linarith
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw_big; linarith
  have hwslit : w ∈ slitPlane := hsw.mem_slitPlane hs hw0
  refine ⟨(exp_logGammaS hwslit).symm, ?_⟩
  -- u and its size
  set u : ℂ := (β : ℂ) / (n * α) with hudef
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hnαne : (n : ℂ) * α ≠ 0 := mul_ne_zero hnC hα0
  have hunorm : ‖u‖ = β / (n * ‖α‖) := by
    rw [hudef, norm_div, hnα, Complex.norm_of_nonneg hβ0.le]
  have hu2 : ‖u‖ ≤ 2 / (a * n) := by
    rw [hunorm]
    apply div_le_div₀ (by norm_num) hβ2 (by positivity) hna
  have hu12 : ‖u‖ ≤ 1 / 2 := by
    calc ‖u‖ ≤ 2 / (a * n) := hu2
      _ ≤ 2 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hX
      _ = 1 / 2 := by norm_num
  -- logarithm splitting
  have hw_eq : w = (n : ℂ) * (α * (1 + u)) := by
    rw [hwdef, hudef]; field_simp
  have h1u : 1 + u ≠ 0 := by
    intro h
    have : ‖(1 : ℂ) + u‖ ≥ 1 / 2 := by
      have := norm_sub_norm_le (1 : ℂ) (-u)
      simp at this
      linarith
    rw [h, norm_zero] at this; linarith
  have hlogw : log w = (Real.log n : ℂ) + (log α + log (1 + u)) := by
    rw [hw_eq, log_ofReal_mul hn0 (mul_ne_zero hα0 h1u)]
    rw [log_mul_one_add hα0 hβ0 hn0 hu12]
  have hnu : (n : ℂ) * α * u = β := by rw [hudef]; field_simp
  -- the error identity
  have herr : logGammaS w -
        ((n : ℂ) * α * (Real.log n : ℂ) + n * (α * log α - α) +
          (β - 1 / 2) * ((Real.log n : ℂ) + log α) + (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ)) =
      J w + (n : ℂ) * α * (log (1 + u) - u) + ((β : ℂ) - 1 / 2) * log (1 + u) := by
    unfold logGammaS
    rw [hlogw, hwdef]
    linear_combination hnu
  rw [herr]
  -- the three bounds
  have hJ : ‖J w‖ ≤ 1 / (6 * s ^ 2 * (a * n)) := by
    calc ‖J w‖ ≤ 1 / (12 * s ^ 2 * ‖w‖) := norm_J_le hs hw0 hsw
      _ ≤ 1 / (12 * s ^ 2 * (a * n / 2)) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact mul_le_mul_of_nonneg_left hw_big (by positivity)
      _ = 1 / (6 * s ^ 2 * (a * n)) := by ring
  have hT1 : ‖(n : ℂ) * α * (log (1 + u) - u)‖ ≤ 4 / (a * n) := by
    have hb := norm_log_one_add_sub_self_le (z := u) (by linarith)
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    rw [norm_mul, hnα]
    calc n * ‖α‖ * ‖log (1 + u) - u‖ ≤ n * ‖α‖ * (‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2) := by gcongr
      _ ≤ n * ‖α‖ * (‖u‖ ^ 2 * 2 / 2) := by gcongr
      _ = β ^ 2 / (n * ‖α‖) := by rw [hunorm]; field_simp
      _ ≤ 4 / (a * n) := by
          apply div_le_div₀ (by norm_num) (by nlinarith) (by positivity) hna
  have hT2 : ‖((β : ℂ) - 1 / 2) * log (1 + u)‖ ≤ 9 / 2 / (a * n) := by
    have hb := norm_log_one_add_half_le_self hu12
    have hβn : ‖(β : ℂ) - 1 / 2‖ ≤ 3 / 2 := by
      rw [show (β : ℂ) - 1 / 2 = ((β - 1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    rw [norm_mul]
    calc ‖(β : ℂ) - 1 / 2‖ * ‖log (1 + u)‖ ≤ 3 / 2 * (3 / 2 * ‖u‖) := by gcongr
      _ ≤ 3 / 2 * (3 / 2 * (2 / (a * n))) := by gcongr
      _ = 9 / 2 / (a * n) := by ring
  calc ‖J w + (n : ℂ) * α * (log (1 + u) - u) + ((β : ℂ) - 1 / 2) * log (1 + u)‖
      ≤ ‖J w‖ + ‖(n : ℂ) * α * (log (1 + u) - u)‖ + ‖((β : ℂ) - 1 / 2) * log (1 + u)‖ :=
        norm_add₃_le
    _ ≤ 1 / (6 * s ^ 2 * (a * n)) + 4 / (a * n) + 9 / 2 / (a * n) := by linarith
    _ = (17 / 2 + 1 / (6 * s ^ 2)) / (a * n) := by
        have hpos : 0 < a * n := by positivity
        field_simp
        ring
    _ ≤ (9 + 1 / (6 * s ^ 2)) / (a * n) := by
        have hpos : 0 < a * n := by positivity
        exact div_le_div_of_nonneg_right (by linarith) hpos.le

end ZetaIrr.Stirling
