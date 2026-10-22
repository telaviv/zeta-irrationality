/-
# Uniform complex Stirling in sectors, with the sharp DLMF constant

Main theorem `norm_J_le`: if `‖t + w‖ ≥ s (t + ‖w‖)` for all `t ≥ 0` (`SectorBound s w`; for
`|arg w| ≤ π - φ` one may take `s = sin(φ/2)`, `sectorBound_of_arg`), then the remainder
`J w = logGammaS w - ((w - 1/2) log w - w + (1/2) log 2π)` satisfies

    ‖J w‖ ≤ 1 / (12 s² ‖w‖).

This is DLMF §5.11(ii) (remainder bound for 5.11.1 with N = 1, in the form |ϱ| ≤ 1/(12|w| sin²(φ/2))).

Route: `J w = ∫_0^∞ Q(t)/(t+w)^2 dt` with `Q = {t}(1-{t})/2 ≥ 0`; `‖t + w‖ ≥ sin(φ/2)(t + ‖w‖)`;
and `∫_0^∞ Q(t)/(t+r)^2 dt ≤ 1/(12 r)`, proved period by period from
`(x + 1/2) log(1 + 1/x) - 1 ≤ 1/(12x) - 1/(12(x+1))` (series for `log(1 + 1/x)`).
-/
import ZetaIrrational.Stirling.LogGamma

namespace ZetaIrr.Stirling

open Complex Set MeasureTheory Filter Topology

/-- The real integral of the kernel over one period. -/
theorem integral_piece_real {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ∫ t in (k : ℝ)..(k + 1), kerQ t / (t + r) ^ 2 =
      (r + k + 1 / 2) * (Real.log (r + k + 1) - Real.log (r + k)) - 1 := by
  set a : ℝ := r + k with ha
  set b : ℝ := r + k + 1 with hb
  have hk : (k : ℝ) ≤ k + 1 := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : ∀ t ∈ uIcc (k : ℝ) (k + 1), 0 < t + r := by
    intro t ht
    rw [uIcc_of_le hk] at ht
    linarith [ht.1]
  let F : ℝ → ℝ := fun t =>
    -(t + r) / 2 + (a + b) / 2 * Real.log (t + r) + a * b * (2 * (t + r))⁻¹
  have hF : ∀ t ∈ uIcc (k : ℝ) (k + 1),
      HasDerivAt F ((t - k) * (k + 1 - t) / 2 / (t + r) ^ 2) t := by
    intro t ht
    have hu : HasDerivAt (fun t : ℝ => t + r) 1 t := (hasDerivAt_id t).add_const r
    have hz := (hpos t ht).ne'
    have h1 := hu.neg.div_const 2
    have h2 := (hu.log hz).const_mul ((a + b) / 2)
    have h3 := ((hu.const_mul 2).inv (mul_ne_zero two_ne_zero hz)).const_mul (a * b)
    have hsum := (h1.add h2).add h3
    refine hsum.congr_deriv ?_
    rw [ha, hb]
    field_simp
    ring
  have hcongr : ∫ t in (k : ℝ)..(k + 1), kerQ t / (t + r) ^ 2 =
      ∫ t in (k : ℝ)..(k + 1), (t - k) * (k + 1 - t) / 2 / (t + r) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hk] at ht
    simp only [kerQ_eq_of_mem k ht]
  have hcont : ContinuousOn (fun t : ℝ => (t - k) * (k + 1 - t) / 2 / (t + r) ^ 2)
      (uIcc (k : ℝ) (k + 1)) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (hpos t ht).ne'
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
  have ha0 : r + k ≠ 0 := by positivity
  have hb0 : r + k + 1 ≠ 0 := by positivity
  simp only [F]
  rw [show (k : ℝ) + 1 + r = r + k + 1 by ring, show (k : ℝ) + r = r + k by ring, ha, hb]
  field_simp
  ring

/-- `(x + 1/2) log(1 + 1/x) - 1 ≤ 1/(12x) - 1/(12(x+1))` for `x > 0`. -/
lemma piece_le {x : ℝ} (hx : 0 < x) :
    (x + 1 / 2) * Real.log (1 + x⁻¹) - 1 ≤ 1 / (12 * x) - 1 / (12 * (x + 1)) := by
  set y : ℝ := 1 / (2 * x + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  have h := Real.hasSum_log_one_add_inv hx
  rw [← hy] at h
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * k + 1)) * y ^ (2 * k + 1) with hf
  have h1 : HasSum (fun k => f (k + 1)) (Real.log (1 + x⁻¹) - ∑ i ∈ Finset.range 1, f i) :=
    (hasSum_nat_add_iff' 1).mpr h
  have hg : HasSum (fun k : ℕ => (2 / 3 * y ^ 3) * (y ^ 2) ^ k) ((2 / 3 * y ^ 3) * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (sq_nonneg y) hy2).mul_left _
  have hle : ∀ k : ℕ, f (k + 1) ≤ (2 / 3 * y ^ 3) * (y ^ 2) ^ k := by
    intro k
    simp only [hf]
    have hk : (1 : ℝ) / (2 * ((k + 1 : ℕ) : ℝ) + 1) ≤ 1 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hyk : 0 ≤ y ^ (2 * (k + 1) + 1) := by positivity
    calc 2 * (1 / (2 * ((k + 1 : ℕ) : ℝ) + 1)) * y ^ (2 * (k + 1) + 1)
        ≤ 2 * (1 / 3) * y ^ (2 * (k + 1) + 1) := by gcongr
      _ = (2 / 3 * y ^ 3) * (y ^ 2) ^ k := by rw [← pow_mul]; ring
  have hsum := hasSum_le hle h1 hg
  simp only [Finset.sum_range_one, hf, Nat.cast_zero, mul_zero, zero_add, pow_one] at hsum
  -- hsum : log (1 + x⁻¹) - 2 * (1/1) * y ≤ 2/3 y^3 (1 - y^2)⁻¹
  have h1y : 1 - y ^ 2 = 4 * x * (x + 1) * y ^ 2 := by
    rw [hy]; field_simp; ring
  rw [h1y] at hsum
  have hL : Real.log (1 + x⁻¹) ≤ 2 * y + 2 / 3 * y ^ 3 * (4 * x * (x + 1) * y ^ 2)⁻¹ := by
    linarith
  have hx12 : 0 ≤ x + 1 / 2 := by linarith
  calc (x + 1 / 2) * Real.log (1 + x⁻¹) - 1
      ≤ (x + 1 / 2) * (2 * y + 2 / 3 * y ^ 3 * (4 * x * (x + 1) * y ^ 2)⁻¹) - 1 := by
        gcongr
    _ = 1 / (12 * x) - 1 / (12 * (x + 1)) := by
        rw [hy]; field_simp; ring

/-- `∫_0^∞ Q(t)/(t + r)^2 dt ≤ 1/(12 r)`, with integrability. -/
theorem integral_kerQ_le {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => kerQ t / (t + r) ^ 2) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), kerQ t / (t + r) ^ 2 ≤ 1 / (12 * r) := by
  obtain ⟨hint0, -⟩ := integral_inv_add_pow hr (le_refl 2)
  have hint : IntegrableOn (fun t : ℝ => kerQ t / (t + r) ^ 2) (Ioi 0) := by
    refine Integrable.mono' (hint0.const_mul (1 / 8))
      ((measurable_kerQ.div ((measurable_id.add_const r).pow_const 2)).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ (fun t ht => ?_)
    simp only [mem_Ioi] at ht
    have htr : 0 < t + r := by linarith
    rw [Real.norm_of_nonneg (div_nonneg (kerQ_nonneg t) (by positivity))]
    calc kerQ t / (t + r) ^ 2 ≤ (1 / 8) / (t + r) ^ 2 :=
          div_le_div_of_nonneg_right (kerQ_le t) (by positivity)
      _ = 1 / 8 * (1 / (t + r) ^ 2) := by ring
  refine ⟨hint, ?_⟩
  have hpart : ∀ n : ℕ, ∫ t in (0 : ℝ)..n, kerQ t / (t + r) ^ 2 ≤ 1 / (12 * r) := by
    intro n
    have hII : ∀ k < n, IntervalIntegrable (fun t : ℝ => kerQ t / (t + r) ^ 2) volume
        ((fun k : ℕ => (k : ℝ)) k) ((fun k : ℕ => (k : ℝ)) (k + 1)) := by
      intro k _
      simp only
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)]
      exact hint.mono_set (fun t ht => lt_of_le_of_lt (Nat.cast_nonneg k) ht.1)
    have hsum := intervalIntegral.sum_integral_adjacent_intervals hII
    simp only [Nat.cast_zero] at hsum
    rw [← hsum]
    have htel := Finset.sum_range_sub' (fun k : ℕ => 1 / (12 * (r + k))) n
    calc ∑ k ∈ Finset.range n, ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), kerQ t / (t + r) ^ 2
        ≤ ∑ k ∈ Finset.range n, (1 / (12 * (r + k)) - 1 / (12 * (r + (k + 1 : ℕ)))) := by
          apply Finset.sum_le_sum
          intro k _
          push_cast
          rw [integral_piece_real hr k]
          have hrk : 0 < r + k := by positivity
          have e : Real.log (r + k + 1) - Real.log (r + k) = Real.log (1 + (r + k)⁻¹) := by
            rw [← Real.log_div (by positivity) hrk.ne']
            congr 1
            field_simp
          rw [e, show r + (k : ℝ) + 1 / 2 = (r + k) + 1 / 2 by ring]
          have := piece_le hrk
          rw [show r + ((k : ℝ) + 1) = (r + k) + 1 by ring]
          exact this
      _ = 1 / (12 * (r + ((0 : ℕ) : ℝ))) - 1 / (12 * (r + n)) := htel
      _ ≤ 1 / (12 * r) := by
          have : 0 ≤ 1 / (12 * (r + n)) := by positivity
          simp only [Nat.cast_zero, add_zero]
          linarith
  exact le_of_tendsto' (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop)
    hpart

/-- **Sharp remainder bound**: `‖J w‖ ≤ 1/(12 s² ‖w‖)` under the sector bound with constant `s`. -/
theorem norm_J_le {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ≠ 0) (h : SectorBound s w) :
    ‖J w‖ ≤ 1 / (12 * s ^ 2 * ‖w‖) := by
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨hint, hle⟩ := integral_kerQ_le hr
  unfold J Jm
  calc ‖∫ t in Ioi (0 : ℝ), (kerQ t : ℂ) / ((t : ℂ) + w) ^ 2‖
      ≤ ∫ t in Ioi (0 : ℝ), (1 / s ^ 2) * (kerQ t / (t + ‖w‖) ^ 2) := by
        apply norm_integral_le_of_norm_le (hint.const_mul _)
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine ae_of_all _ (fun t ht => ?_)
        simp only [mem_Ioi] at ht
        have hb := h t ht.le
        rw [norm_div, norm_pow, Complex.norm_of_nonneg (kerQ_nonneg t)]
        have hst : 0 < s * (t + ‖w‖) := mul_pos hs (by linarith)
        calc kerQ t / ‖(t : ℂ) + w‖ ^ 2 ≤ kerQ t / (s * (t + ‖w‖)) ^ 2 := by
              apply div_le_div_of_nonneg_left (kerQ_nonneg t) (by positivity)
              exact pow_le_pow_left₀ hst.le hb 2
          _ = (1 / s ^ 2) * (kerQ t / (t + ‖w‖) ^ 2) := by rw [mul_pow]; field_simp
    _ = (1 / s ^ 2) * ∫ t in Ioi (0 : ℝ), kerQ t / (t + ‖w‖) ^ 2 := integral_const_mul _ _
    _ ≤ (1 / s ^ 2) * (1 / (12 * ‖w‖)) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 / (12 * s ^ 2 * ‖w‖) := by field_simp

end ZetaIrr.Stirling
