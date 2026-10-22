/-
# Deformation of the concrete Z7 contour

`contour_eq_polyline_Gfn`: let `c > 0` be a non-integer and `w 0 = c, w 1, …, w K` a polyline
whose points other than `w 0` lie in the open upper half plane, with `Re (w K) > 0`. Then

    i ∫_0^∞ G_n(c + iy) dy = Σ_{k<K} ∫_{[w_k, w_{k+1}]} G_n + i ∫_0^∞ G_n(w_K + iy) dy,

where `G_n = R_n k₄` is holomorphic on `{Im z > 0} ∪ B(c, δ)`. Mirrors lean_beta's
`I3/Analytic/Deform.lean`; the kernel bound in the upper half plane is
`‖k₄(z)‖ ≤ 24 π⁵ (1 + 1/(π y₀))⁵` for `Im z ≥ y₀` (`norm_kk4_le_of_im`).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Analytic.ContourZ7
import ZetaIrrational.Analytic.Deformation

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Real MeasureTheory Set Filter Topology Metric
open ZetaIrr.Analytic ZetaIrr.Fam.Analytic

lemma not_mem_poles_of_im (m : ℕ) {z : ℂ} (hz : 0 < z.im) : z ∉ poles m := by
  rintro ⟨k, _, _, rfl⟩; simp at hz

/-- `G_n` is holomorphic at every point of the open upper half plane. -/
lemma Gfn_differentiableAt_of_im (m : ℕ) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (Gfn m) z := by
  have h0 := RCd_differentiableAt m 0 (not_mem_poles_of_im m hz)
  have h1 := differentiableAt_kk 4 (sin_pi_ne_zero_of_im hz.ne')
  have hf : Gfn m = fun w => RCd m 0 w * kk 4 w := by funext w; rfl
  rw [hf]
  exact h0.mul h1

/-- The kernel bound away from the real axis. -/
lemma norm_kk4_le_of_im {z : ℂ} {y₀ : ℝ} (hy₀ : 0 < y₀) (hz : y₀ ≤ z.im) :
    ‖kk 4 z‖ ≤ 24 * π ^ 5 * (1 + 1 / (π * y₀)) ^ 5 := by
  have h := norm_cotP_cscP_le_of_im (z := z) hy₀ (hz.trans (le_abs_self _))
  have hB : 1 ≤ 1 + 1 / (π * y₀) := by
    have : 0 ≤ 1 / (π * y₀) := by have := Real.pi_pos; positivity
    linarith
  exact norm_kk_le 4 hB h.1 h.2

/-- `‖G_n(z)‖ ≤ C K(y₀) (1 + ‖z‖²)⁻¹` for `Re z ≥ c`, `Im z ≥ y₀`. -/
lemma norm_Gfn_le_of_im (m : ℕ) {c C : ℝ}
    (hC : ∀ z : ℂ, c ≤ z.re → ‖RCd m 0 z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) {z : ℂ} {y₀ : ℝ}
    (hy₀ : 0 < y₀) (hzre : c ≤ z.re) (hz : y₀ ≤ z.im) :
    ‖Gfn m z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹ * (24 * π ^ 5 * (1 + 1 / (π * y₀)) ^ 5) := by
  have hG : Gfn m z = RCd m 0 z * kk 4 z := rfl
  rw [hG, norm_mul]
  have h1 := hC z hzre
  have hC0 : 0 ≤ C * (1 + ‖z‖ ^ 2)⁻¹ := (norm_nonneg _).trans h1
  exact mul_le_mul h1 (norm_kk4_le_of_im hy₀ hz) (norm_nonneg _) hC0

theorem contour_eq_polyline_Gfn (m : ℕ) {c : ℝ} (hc0 : 0 < c) (hcZ : ∀ k : ℤ, c ≠ k)
    (w : ℕ → ℂ) (K : ℕ) (hw0 : w 0 = c)
    (hseg : ∀ k < K, ∀ t ∈ Ioc (0 : ℝ) 1, 0 < (w k + t * (w (k + 1) - w k)).im)
    (hKim : 0 < (w K).im) (hKre : 0 < (w K).re) :
    I * ∫ y in Ioi (0 : ℝ), Gfn m (c + y * I)
      = (∑ k ∈ Finset.range K, segInt (Gfn m) (w k) (w (k + 1)))
        + I * ∫ y in Ioi (0 : ℝ), Gfn m (w K + y * I) := by
  set δ : ℝ := min (c - ⌊c⌋) (⌈c⌉ - c) / 2 with hδ
  have hfl : (⌊c⌋ : ℝ) < c := lt_of_le_of_ne (Int.floor_le c) (fun h => hcZ _ h.symm)
  have hcl : c < (⌈c⌉ : ℝ) := lt_of_le_of_ne (Int.le_ceil c) (fun h => hcZ _ h)
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min (by linarith) (by linarith))
  have hδ1 : δ ≤ (c - ⌊c⌋) / 2 := by rw [hδ]; gcongr; exact min_le_left _ _
  have hδ2 : δ ≤ (⌈c⌉ - c) / 2 := by rw [hδ]; gcongr; exact min_le_right _ _
  set U : Set ℂ := {z : ℂ | 0 < z.im} ∪ ball (c : ℂ) δ with hU
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).union isOpen_ball
  have hball_re : ∀ z ∈ ball (c : ℂ) δ, c - δ < z.re ∧ z.re < c + δ := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h := Complex.abs_re_le_norm (z - c)
    have : (z - c).re = z.re - c := by simp
    rw [this] at h
    have := abs_lt.1 (h.trans_lt hz)
    constructor <;> linarith [this.1, this.2]
  have hFdiff : DifferentiableOn ℂ (Gfn m) U := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases hz with hz | hz
    · exact Gfn_differentiableAt_of_im m hz
    · obtain ⟨h1, h2⟩ := hball_re z hz
      have hfl0 : (0 : ℝ) ≤ ⌊c⌋ := by exact_mod_cast Int.floor_nonneg.2 hc0.le
      have hnp : z ∉ poles m := fun hp => by
        have := re_le_of_mem_poles hp; linarith
      have hsin : Complex.sin (π * z) ≠ 0 := by
        refine sin_pi_ne_zero_of_re (fun k hk => ?_)
        rw [hk] at h1 h2
        have hk1 : (⌊c⌋ : ℝ) < k := by linarith
        have hk2 : (k : ℝ) < ⌈c⌉ := by linarith
        have hk1' : ⌊c⌋ < k := by exact_mod_cast hk1
        have hk2' : k < ⌈c⌉ := by exact_mod_cast hk2
        have : ⌈c⌉ ≤ ⌊c⌋ + 1 := Int.ceil_le_floor_add_one c
        omega
      have hf : Gfn m = fun w => RCd m 0 w * kk 4 w := by funext w; rfl
      rw [hf]
      exact (RCd_differentiableAt m 0 hnp).mul (differentiableAt_kk 4 hsin)
  obtain ⟨P, hP⟩ := exists_prim_upper_union_ball (F := Gfn m) c δ hδ0 hFdiff
  set c' : ℝ := min c (w K).re with hc'
  have hc'0 : 0 < c' := lt_min hc0 hKre
  obtain ⟨C, hC⟩ := RCd_bound m 0 (c := c') (by linarith)
  have hC0 : 0 ≤ C := by
    have := hC ((c : ℂ)) (by simp [hc'])
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) (by positivity)
  set K1 : ℝ := 24 * π ^ 5 * (1 + 1 / (π * 1)) ^ 5 with hK1
  have hK10 : 0 ≤ K1 := by rw [hK1]; have := Real.pi_pos; positivity
  rw [show (c : ℂ) = w 0 from hw0.symm]
  refine ray_eq_polyline_add_ray hUopen hFdiff hP w K ?_ ?_ ?_ ?_ ?_ (fun Y => C * K1 / Y)
    (tendsto_const_nhds.div_atTop tendsto_id) ?_
  · intro k hk t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; rw [hw0]; right; exact (mem_ball_self hδ0 : (c : ℂ) ∈ ball (c : ℂ) δ)
      · left
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk0
        have := hseg j (by omega) 1 ⟨one_pos, le_rfl⟩
        simp only [Complex.ofReal_one, one_mul, add_sub_cancel] at this
        simpa using this
    · left; exact hseg k hk t ⟨h0, ht.2⟩
  · intro y hy
    rcases eq_or_lt_of_le hy with h0 | h0
    · subst h0; rw [hw0]; right; simpa using (mem_ball_self hδ0 : (c : ℂ) ∈ ball (c : ℂ) δ)
    · left; rw [hw0]; simpa using h0
  · intro y hy; left; simp; linarith
  · -- integrability on the ray from `c`: the line is integrable (`ContourZ7`)
    have hs := sin_real_ne_zero hcZ
    obtain ⟨C₂, hC₂⟩ := RCd_bound m 0 (c := c) (by linarith)
    have hcontR : Continuous (fun y : ℝ => Gfn m ((c : ℂ) + y * I)) := by
      rw [continuous_iff_continuousAt]
      intro y
      have hnp : ((c : ℂ) + y * I) ∉ poles m := mem_compl_poles_of_re (by simp; linarith)
      have hf : Gfn m = fun w => RCd m 0 w * kk 4 w := by funext w; rfl
      rw [hf]
      exact ContinuousAt.comp (g := fun w => RCd m 0 w * kk 4 w)
        ((RCd_differentiableAt m 0 hnp).mul (differentiableAt_kk 4
          (sin_ne_zero_of_line hcZ y))).continuousAt (continuous_line c).continuousAt
    have hC₂0 : 0 ≤ C₂ := by
      have := hC₂ ((c : ℂ)) (by simp)
      exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans this) (by positivity)
    have hint : Integrable (fun y : ℝ => Gfn m ((c : ℂ) + y * I)) := by
      refine integrable_of_bound_inv_one_add_sq
        (C := C₂ * (24 * π ^ 5 * (1 / |Real.sin (π * c)|) ^ 5)) hcontR (fun y => ?_)
      have hG : Gfn m ((c : ℂ) + y * I) = RCd m 0 ((c : ℂ) + y * I) * kk 4 ((c : ℂ) + y * I) :=
        rfl
      rw [hG, norm_mul]
      have h1 := (hC₂ _ (by simp)).trans
        (mul_le_mul_of_nonneg_left (inv_one_add_norm_sq_le c y) hC₂0)
      have h2 := norm_kk_line_le hcZ 4 y
      calc ‖RCd m 0 (c + y * I)‖ * ‖kk 4 (c + y * I)‖
          ≤ C₂ * (1 + y ^ 2)⁻¹ * (24 * π ^ 5 * (1 / |Real.sin (π * c)|) ^ 5) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    rw [hw0]
    exact hint.integrableOn
  · -- integrability on the ray from `w K`
    set y₀ := (w K).im with hy₀
    set Ky : ℝ := 24 * π ^ 5 * (1 + 1 / (π * y₀)) ^ 5 with hKy
    have hbound : ∀ y ∈ Ioi (0 : ℝ), ‖Gfn m (w K + y * I)‖ ≤ C * Ky * (1 + y ^ 2)⁻¹ := by
      intro y hy
      have hy0 : 0 < y := hy
      have him : (w K + y * I).im = (w K).im + y := by simp
      have hre : (w K + y * I).re = (w K).re := by simp
      have h := norm_Gfn_le_of_im m hC (z := w K + y * I) hKim
        (by rw [hre]; exact min_le_right _ _) (by rw [him]; linarith)
      refine h.trans ?_
      have h1 : (1 + ‖w K + y * I‖ ^ 2)⁻¹ ≤ (1 + y ^ 2)⁻¹ := by
        apply inv_anti₀ (by positivity)
        have := Complex.abs_im_le_norm (w K + y * I)
        rw [him, abs_of_pos (by linarith)] at this
        have : y ^ 2 ≤ ‖w K + y * I‖ ^ 2 := pow_le_pow_left₀ hy0.le (by linarith) 2
        linarith
      have hKy0 : 0 ≤ Ky := by rw [hKy]; have := Real.pi_pos; positivity
      calc C * (1 + ‖w K + y * I‖ ^ 2)⁻¹ * Ky ≤ C * (1 + y ^ 2)⁻¹ * Ky := by gcongr
        _ = C * Ky * (1 + y ^ 2)⁻¹ := by ring
    have hcont : ContinuousOn (fun y : ℝ => Gfn m (w K + y * I)) (Ioi 0) := by
      intro y hy
      have hy0 : 0 < y := hy
      have : 0 < (w K + y * I).im := by simp; linarith
      exact (ContinuousAt.comp (g := Gfn m) (f := fun y : ℝ => w K + y * I)
        (Gfn_differentiableAt_of_im m this).continuousAt (by fun_prop)).continuousWithinAt
    exact (integrable_inv_one_add_sq.const_mul _).integrableOn.mono'
      (hcont.aestronglyMeasurable measurableSet_Ioi)
      (ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  · -- horizontal segments
    filter_upwards [eventually_ge_atTop 1] with Y hY
    intro t ht
    set z := w 0 + Y * I + t * (((w K).re - (w 0).re : ℝ) : ℂ) with hz
    have him : z.im = Y := by rw [hz, hw0]; simp
    have hre : z.re = c + t * ((w K).re - c) := by rw [hz, hw0]; simp
    have hzre : c' ≤ z.re := by
      rw [hre]
      rcases le_total c (w K).re with h | h
      · have : 0 ≤ t * ((w K).re - c) := mul_nonneg ht.1 (by linarith)
        have : c' ≤ c := min_le_left _ _
        linarith
      · have : c' ≤ (w K).re := min_le_right _ _
        have : t * ((w K).re - c) ≥ (w K).re - c := by nlinarith [ht.2]
        linarith
    refine ⟨Or.inl (by rw [Set.mem_ofPred_eq, him]; linarith), ?_⟩
    have h := norm_Gfn_le_of_im m hC (z := z) one_pos hzre (by rw [him]; exact hY)
    refine h.trans ?_
    have hzY : Y ≤ ‖z‖ := by
      have := Complex.abs_im_le_norm z
      rw [him, abs_of_pos (by linarith)] at this; exact this
    have : (1 + ‖z‖ ^ 2)⁻¹ ≤ 1 / Y := by
      rw [one_div]
      apply inv_anti₀ (by linarith)
      nlinarith
    calc C * (1 + ‖z‖ ^ 2)⁻¹ * K1 ≤ C * (1 / Y) * K1 := by gcongr
      _ = C * K1 / Y := by ring

end ZetaIrr.Z7.Analytic
