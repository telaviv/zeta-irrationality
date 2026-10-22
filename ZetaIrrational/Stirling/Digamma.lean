/-
# Derivatives: `logGammaS` is holomorphic, and uniform bounds for ψ and ψ′ in sectors

* `hasDerivAt_Jm`: `d/dw Jm m w = -m Jm (m+1) w` on the slit plane (differentiation under ∫).
* `hasDerivAt_logGammaS`: `logGammaS' = log w - 1/(2w) - 2 Jm 3 w`; so `logGammaS` is holomorphic on
  the slit plane, and `logGammaS_ofReal`: it equals `Real.log (Real.Gamma x)` on `(0, ∞)`.
  Hence `logGammaS` is *the* principal branch of `log Γ` on the slit plane.
* `digamma_eq`: `ψ(w) = log w - 1/(2w) - 2 Jm 3 w`;
  `hasDerivAt_digamma`: `ψ'(w) = 1/w + 1/(2w²) + 6 Jm 4 w`.
* Sector bounds (`|arg w| ≤ π - φ`, `s = sin(φ/2)`):
  - `digamma_sector`: `‖ψ(w) - (log w - 1/(2w))‖ ≤ 1/(8 s³ ‖w‖²)`;
  - `deriv_digamma_sector`: `‖ψ'(w) - (1/w + 1/(2w²))‖ ≤ 1/(4 s⁴ ‖w‖³)`;
  - `deriv_digamma_sector'`: for `‖w‖ ≥ 1`, `‖ψ'(w) - 1/w‖ ≤ (1/2 + 1/(4 s⁴)) / ‖w‖²`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Stirling.Bound
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace ZetaIrr.Stirling

open Complex Set MeasureTheory Filter Topology Metric

lemma hasDerivAt_integrand (m : ℕ) (hm : 2 ≤ m) (t : ℝ) {x : ℂ} (hx : (t : ℂ) + x ≠ 0) :
    HasDerivAt (fun x : ℂ => (kerQ t : ℂ) / ((t : ℂ) + x) ^ m)
      (-(m : ℂ) * ((kerQ t : ℂ) / ((t : ℂ) + x) ^ (m + 1))) x := by
  have hu : HasDerivAt (fun x : ℂ => (t : ℂ) + x) 1 x := (hasDerivAt_id x).const_add _
  have h := (hasDerivAt_const x (kerQ t : ℂ)).div (hu.pow m) (pow_ne_zero m hx)
  refine h.congr_deriv ?_
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, Pi.pow_apply]
  push_cast
  field_simp
  ring

/-- Differentiation under the integral sign: `Jm m' = -m Jm (m+1)`. -/
theorem hasDerivAt_Jm {w : ℂ} (hw : w ∈ slitPlane) {m : ℕ} (hm : 2 ≤ m) :
    HasDerivAt (Jm m) (-(m : ℂ) * Jm (m + 1) w) w := by
  obtain ⟨σ, hσ, hsb⟩ := exists_sectorBound hw
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set ε := σ * ‖w‖ / 2 with hε
  have hε0 : 0 < ε := by positivity
  -- lower bound on the ball
  have hlow : ∀ x ∈ ball w ε, ∀ t : ℝ, 0 ≤ t → σ * (t + ‖w‖ / 2) ≤ ‖(t : ℂ) + x‖ := by
    intro x hx t ht
    have h1 := hsb t ht
    have h2 : ‖(t : ℂ) + w‖ ≤ ‖(t : ℂ) + x‖ + ‖x - w‖ := by
      calc ‖(t : ℂ) + w‖ = ‖((t : ℂ) + x) - (x - w)‖ := by ring_nf
        _ ≤ ‖(t : ℂ) + x‖ + ‖x - w‖ := norm_sub_le _ _
    have h3 : ‖x - w‖ < ε := by rwa [mem_ball, dist_eq_norm] at hx
    nlinarith
  have hne : ∀ x ∈ ball w ε, ∀ t : ℝ, 0 ≤ t → (t : ℂ) + x ≠ 0 := by
    intro x hx t ht
    have := hlow x hx t ht
    have : 0 < σ * (t + ‖w‖ / 2) := by positivity
    exact norm_pos_iff.mp (by linarith)
  obtain ⟨hbint, -⟩ := integral_inv_add_pow (half_pos hr) (show 2 ≤ m + 1 by omega)
  set bound : ℝ → ℝ := fun t => (m : ℝ) * ((1 / 8) / σ ^ (m + 1)) * (1 / (t + ‖w‖ / 2) ^ (m + 1))
    with hbound
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun x t => (kerQ t : ℂ) / ((t : ℂ) + x) ^ m)
    (F' := fun x t => -(m : ℂ) * ((kerQ t : ℂ) / ((t : ℂ) + x) ^ (m + 1)))
    (x₀ := w) (bound := bound) (ball_mem_nhds w hε0)
    (Eventually.of_forall (fun x => (measurable_integrand m x).aestronglyMeasurable))
    (integrable_Jm hσ hw0 hsb hm)
    ((measurable_const.mul (measurable_integrand (m + 1) w)).aestronglyMeasurable)
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ (fun t ht x hx => ?_)
      simp only [mem_Ioi] at ht
      have hb := hlow x hx t ht.le
      have hst : 0 < σ * (t + ‖w‖ / 2) := by positivity
      rw [norm_mul, norm_neg, Complex.norm_natCast, norm_div, norm_pow,
        Complex.norm_of_nonneg (kerQ_nonneg t)]
      simp only [hbound]
      have : kerQ t / ‖(t : ℂ) + x‖ ^ (m + 1) ≤ (1 / 8) / σ ^ (m + 1) * (1 / (t + ‖w‖ / 2) ^ (m + 1)) := by
        calc kerQ t / ‖(t : ℂ) + x‖ ^ (m + 1) ≤ (1 / 8) / (σ * (t + ‖w‖ / 2)) ^ (m + 1) := by
              apply div_le_div₀ (by norm_num) (kerQ_le t) (by positivity)
              exact pow_le_pow_left₀ hst.le hb _
          _ = (1 / 8) / σ ^ (m + 1) * (1 / (t + ‖w‖ / 2) ^ (m + 1)) := by
              rw [mul_pow]; field_simp
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg m))
    (hbint.const_mul _)
    (by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ (fun t ht x hx => ?_)
      simp only [mem_Ioi] at ht
      exact hasDerivAt_integrand m hm t (hne x hx t ht.le))
  have := key.2
  rw [integral_const_mul] at this
  exact this

/-- The derivative of `logGammaS`. -/
theorem hasDerivAt_logGammaS {w : ℂ} (hw : w ∈ slitPlane) :
    HasDerivAt logGammaS (log w - 1 / (2 * w) - 2 * Jm 3 w) w := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hJ := hasDerivAt_Jm hw (le_refl 2)
  have h := ((((hasDerivAt_id w).sub_const (1 / 2 : ℂ)).mul (hasDerivAt_log hw)).sub
    (hasDerivAt_id w)).add_const ((1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ)) |>.add hJ
  unfold logGammaS J
  refine h.congr_deriv ?_
  simp only [id]
  push_cast
  field_simp
  ring

lemma differentiableOn_logGammaS : DifferentiableOn ℂ logGammaS slitPlane :=
  fun _ hw => (hasDerivAt_logGammaS hw).differentiableAt.differentiableWithinAt

lemma Jm_ofReal {x : ℝ} (m : ℕ) :
    Jm m (x : ℂ) = ((∫ t in Ioi (0 : ℝ), kerQ t / (t + x) ^ m : ℝ) : ℂ) := by
  unfold Jm
  rw [← integral_complex_ofReal]
  congr 1
  ext t
  push_cast
  rfl

/-- On the positive real axis `logGammaS` is the real `log Γ`: so `logGammaS` is the principal
branch of `log Γ` on the slit plane. -/
theorem logGammaS_ofReal {x : ℝ} (hx : 0 < x) :
    logGammaS (x : ℂ) = (Real.log (Real.Gamma x) : ℂ) := by
  have hslit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  set L : ℝ := (x - 1 / 2) * Real.log x - x + 1 / 2 * Real.log (2 * Real.pi) +
    ∫ t in Ioi (0 : ℝ), kerQ t / (t + x) ^ 2 with hL
  have hreal : logGammaS (x : ℂ) = (L : ℂ) := by
    unfold logGammaS J
    rw [Jm_ofReal, hL, ← ofReal_log hx.le]
    push_cast
    ring
  have h := exp_logGammaS hslit
  rw [hreal, ← ofReal_exp, Complex.Gamma_ofReal, ofReal_inj] at h
  rw [hreal, ← h, Real.log_exp]

/-- `ψ(w) = log w - 1/(2w) - 2 Jm 3 w` on the slit plane. -/
theorem digamma_eq {w : ℂ} (hw : w ∈ slitPlane) :
    digamma w = log w - 1 / (2 * w) - 2 * Jm 3 w := by
  have hev : Gamma =ᶠ[𝓝 w] (fun z => exp (logGammaS z)) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hw] with z hz using (exp_logGammaS hz).symm
  have hd := ((hasDerivAt_logGammaS hw).cexp).congr_of_eventuallyEq hev
  rw [digamma_def, logDeriv_apply, hd.deriv, exp_logGammaS hw]
  have : Gamma w ≠ 0 := by rw [← exp_logGammaS hw]; exact exp_ne_zero _
  field_simp

/-- `ψ'(w) = 1/w + 1/(2w²) + 6 Jm 4 w` on the slit plane. -/
theorem hasDerivAt_digamma {w : ℂ} (hw : w ∈ slitPlane) :
    HasDerivAt digamma (1 / w + 1 / (2 * w ^ 2) + 6 * Jm 4 w) w := by
  have hw0 : w ≠ 0 := slitPlane_ne_zero hw
  have hev : digamma =ᶠ[𝓝 w] (fun z => log z - 1 / (2 * z) - 2 * Jm 3 z) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hw] with z hz using digamma_eq hz
  have hJ := hasDerivAt_Jm hw (show 2 ≤ 3 by norm_num)
  have h2 : HasDerivAt (fun z : ℂ => 1 / (2 * z)) (-(2 * 1) / (2 * w) ^ 2) w := by
    have := ((hasDerivAt_id w).const_mul (2 : ℂ)).inv (mul_ne_zero two_ne_zero hw0)
    convert this using 1
    · ext z; simp only [one_div]; rfl
    · rfl
  have h := ((hasDerivAt_log hw).sub h2).sub (hJ.const_mul 2)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq hev
  push_cast
  field_simp
  ring

/-! ## Sector bounds -/

theorem norm_Jm3_le {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ≠ 0) (h : SectorBound s w) :
    ‖Jm 3 w‖ ≤ 1 / (16 * s ^ 3 * ‖w‖ ^ 2) := by
  have := norm_Jm_le hs hw h (show 2 ≤ 3 by norm_num)
  convert this using 1
  norm_num
  ring

theorem norm_Jm4_le {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ≠ 0) (h : SectorBound s w) :
    ‖Jm 4 w‖ ≤ 1 / (24 * s ^ 4 * ‖w‖ ^ 3) := by
  have := norm_Jm_le hs hw h (show 2 ≤ 4 by norm_num)
  convert this using 1
  norm_num
  ring

/-- **ψ in sectors**: `‖ψ(w) - (log w - 1/(2w))‖ ≤ 1/(8 sin³(φ/2) ‖w‖²)`. -/
theorem digamma_sector {φ : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi) {w : ℂ} (hw0 : w ≠ 0)
    (harg : |arg w| ≤ Real.pi - φ) :
    ‖digamma w - (log w - 1 / (2 * w))‖ ≤ 1 / (8 * Real.sin (φ / 2) ^ 3 * ‖w‖ ^ 2) := by
  have hw := mem_slitPlane_of_arg hφ0 hw0 harg
  have hs : 0 < Real.sin (φ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hJ := norm_Jm3_le hs hw0 (sectorBound_of_arg hφ0 hφ harg)
  rw [digamma_eq hw, show log w - 1 / (2 * w) - 2 * Jm 3 w - (log w - 1 / (2 * w)) = -(2 * Jm 3 w)
    by ring, norm_neg, norm_mul, Complex.norm_ofNat]
  calc 2 * ‖Jm 3 w‖ ≤ 2 * (1 / (16 * Real.sin (φ / 2) ^ 3 * ‖w‖ ^ 2)) := by gcongr
    _ = 1 / (8 * Real.sin (φ / 2) ^ 3 * ‖w‖ ^ 2) := by field_simp; ring

/-- **ψ′ in sectors**: `‖ψ'(w) - (1/w + 1/(2w²))‖ ≤ 1/(4 sin⁴(φ/2) ‖w‖³)`. -/
theorem deriv_digamma_sector {φ : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi) {w : ℂ} (hw0 : w ≠ 0)
    (harg : |arg w| ≤ Real.pi - φ) :
    ‖deriv digamma w - (1 / w + 1 / (2 * w ^ 2))‖ ≤ 1 / (4 * Real.sin (φ / 2) ^ 4 * ‖w‖ ^ 3) := by
  have hw := mem_slitPlane_of_arg hφ0 hw0 harg
  have hs : 0 < Real.sin (φ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hJ := norm_Jm4_le hs hw0 (sectorBound_of_arg hφ0 hφ harg)
  rw [(hasDerivAt_digamma hw).deriv, show 1 / w + 1 / (2 * w ^ 2) + 6 * Jm 4 w -
    (1 / w + 1 / (2 * w ^ 2)) = 6 * Jm 4 w by ring, norm_mul, Complex.norm_ofNat]
  calc 6 * ‖Jm 4 w‖ ≤ 6 * (1 / (24 * Real.sin (φ / 2) ^ 4 * ‖w‖ ^ 3)) := by gcongr
    _ = 1 / (4 * Real.sin (φ / 2) ^ 4 * ‖w‖ ^ 3) := by field_simp; ring

/-- **ψ′ in sectors, `|w| ≥ 1`**: `‖ψ'(w) - 1/w‖ ≤ (1/2 + 1/(4 sin⁴(φ/2))) / ‖w‖²`. -/
theorem deriv_digamma_sector' {φ : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi) {w : ℂ}
    (hw1 : 1 ≤ ‖w‖) (harg : |arg w| ≤ Real.pi - φ) :
    ‖deriv digamma w - 1 / w‖ ≤ (1 / 2 + 1 / (4 * Real.sin (φ / 2) ^ 4)) / ‖w‖ ^ 2 := by
  have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw1; linarith
  have hr : 0 < ‖w‖ := by linarith
  have hs : 0 < Real.sin (φ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have h := deriv_digamma_sector hφ0 hφ hw0 harg
  have e : deriv digamma w - 1 / w =
      (deriv digamma w - (1 / w + 1 / (2 * w ^ 2))) + 1 / (2 * w ^ 2) := by ring
  have h2 : ‖1 / (2 * w ^ 2)‖ = 1 / (2 * ‖w‖ ^ 2) := by
    rw [norm_div, norm_one, norm_mul, norm_pow, Complex.norm_ofNat]
  have h3 : 1 / (4 * Real.sin (φ / 2) ^ 4 * ‖w‖ ^ 3) ≤ 1 / (4 * Real.sin (φ / 2) ^ 4 * ‖w‖ ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ‖w‖ ^ 2 = ‖w‖ ^ 2 * 1 := by ring
      _ ≤ ‖w‖ ^ 2 * ‖w‖ := by gcongr
      _ = ‖w‖ ^ 3 := by ring
  rw [e]
  calc ‖(deriv digamma w - (1 / w + 1 / (2 * w ^ 2))) + 1 / (2 * w ^ 2)‖
      ≤ ‖deriv digamma w - (1 / w + 1 / (2 * w ^ 2))‖ + ‖1 / (2 * w ^ 2)‖ := norm_add_le _ _
    _ ≤ 1 / (4 * Real.sin (φ / 2) ^ 4 * ‖w‖ ^ 2) + 1 / (2 * ‖w‖ ^ 2) := by
        rw [h2]; linarith
    _ = (1 / 2 + 1 / (4 * Real.sin (φ / 2) ^ 4)) / ‖w‖ ^ 2 := by field_simp; ring

end ZetaIrr.Stirling
