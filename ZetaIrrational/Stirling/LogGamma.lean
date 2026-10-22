/-
# A logarithm of Γ on the slit plane, with the Stirling–Stieltjes representation

`logGammaS w := (w - 1/2) log w - w + (1/2) log(2π) + J w`, `J w = ∫_0^∞ kerQ t/(t+w)^2 dt`.

Main result: `exp_logGammaS : w ∈ slitPlane → exp (logGammaS w) = Gamma w`.

Route: Euler's limit `GammaSeq w n → Γ(w)` (Mathlib), an exact Euler–Maclaurin identity for
`Σ_{j ≤ n} log(w + j)` (`sum_log_eq`, by an explicit antiderivative on each `[k, k+1]`), and
Stirling's formula for `n!` (Mathlib).
-/
import ZetaIrrational.Stirling.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ZetaIrr.Stirling

open Complex Set MeasureTheory Filter Topology

/-- The Stirling-form logarithm of `Γ`. -/
noncomputable def logGammaS (w : ℂ) : ℂ :=
  (w - 1 / 2) * log w - w + (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ) + J w

lemma hasDerivAt_ofReal_add (w : ℂ) (t : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ) + w) 1 t := by
  simpa using (hasDerivAt_id t).ofReal_comp.add_const w

lemma natCast_add_ne_zero {w : ℂ} (hw : w ∈ slitPlane) (j : ℕ) : w + j ≠ 0 := by
  have := ofReal_add_mem_slitPlane hw (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  rw [add_comm] at this
  simpa using slitPlane_ne_zero this

lemma intervalIntegrable_integrand {w : ℂ} (hw : w ∈ slitPlane) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (kerQ t : ℂ) / ((t : ℂ) + w) ^ 2) volume a b := by
  obtain ⟨s, hs, hsb⟩ := exists_sectorBound hw
  have hint := integrable_Jm hs (slitPlane_ne_zero hw) hsb (le_refl 2)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact hint.mono_set (fun t ht => lt_of_le_of_lt ha ht.1)

/-- The integral of the kernel over one period `[k, k+1]`. -/
theorem integral_piece {w : ℂ} (hw : w ∈ slitPlane) (k : ℕ) :
    ∫ t in (k : ℝ)..(k + 1), (kerQ t : ℂ) / ((t : ℂ) + w) ^ 2 =
      (w + k + 1 / 2) * (log (w + (k + 1)) - log (w + k)) - 1 := by
  set a : ℂ := w + k with ha
  set b : ℂ := w + k + 1 with hb
  have hk : (k : ℝ) ≤ k + 1 := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hslit : ∀ t ∈ uIcc (k : ℝ) (k + 1), (t : ℂ) + w ∈ slitPlane := by
    intro t ht
    rw [uIcc_of_le hk] at ht
    exact ofReal_add_mem_slitPlane hw (by linarith [ht.1])
  have hne : ∀ t ∈ uIcc (k : ℝ) (k + 1), (t : ℂ) + w ≠ 0 := fun t ht => slitPlane_ne_zero (hslit t ht)
  let F : ℝ → ℂ := fun t =>
    -((t : ℂ) + w) / 2 + (a + b) / 2 * log ((t : ℂ) + w) + a * b * (2 * ((t : ℂ) + w))⁻¹
  have hF : ∀ t ∈ uIcc (k : ℝ) (k + 1),
      HasDerivAt F ((((t - k) * (k + 1 - t) / 2 : ℝ) : ℂ) / ((t : ℂ) + w) ^ 2) t := by
    intro t ht
    have hu := hasDerivAt_ofReal_add w t
    have h1 := hu.neg.div_const 2
    have h2 := (hu.clog_real (hslit t ht)).const_mul ((a + b) / 2)
    have h3 := ((hu.const_mul 2).inv (mul_ne_zero two_ne_zero (hne t ht))).const_mul (a * b)
    have hsum := (h1.add h2).add h3
    refine hsum.congr_deriv ?_
    have hz := hne t ht
    rw [ha, hb]
    push_cast
    field_simp
    ring
  have hcongr : ∫ t in (k : ℝ)..(k + 1), (kerQ t : ℂ) / ((t : ℂ) + w) ^ 2 =
      ∫ t in (k : ℝ)..(k + 1), (((t - k) * (k + 1 - t) / 2 : ℝ) : ℂ) / ((t : ℂ) + w) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hk] at ht
    simp only [kerQ_eq_of_mem k ht]
  have hcont : ContinuousOn (fun t : ℝ => (((t - k) * (k + 1 - t) / 2 : ℝ) : ℂ) / ((t : ℂ) + w) ^ 2)
      (uIcc (k : ℝ) (k + 1)) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact pow_ne_zero 2 (hne t ht)
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable]
  have e1 : (((k : ℝ) + 1 : ℝ) : ℂ) + w = w + (k + 1) := by push_cast; ring
  have e0 : (((k : ℝ) : ℝ) : ℂ) + w = w + k := by push_cast; ring
  simp only [F, e1, e0]
  have hb0 : w + ((k : ℂ) + 1) ≠ 0 := by
    have := natCast_add_ne_zero hw (k + 1); push_cast at this; exact this
  have ha0 : w + (k : ℂ) ≠ 0 := natCast_add_ne_zero hw k
  rw [ha, hb]
  field_simp
  ring

/-- Exact Euler–Maclaurin identity for `Σ_{j=0}^{n} log(w + j)`. -/
theorem sum_log_eq {w : ℂ} (hw : w ∈ slitPlane) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), log (w + j) =
      (w + n + 1 / 2) * log (w + n) - (w - 1 / 2) * log w - n -
        ∫ t in (0 : ℝ)..n, (kerQ t : ℂ) / ((t : ℂ) + w) ^ 2 := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_integrand hw (le_refl 0) (Nat.cast_nonneg n))
      (intervalIntegrable_integrand hw (Nat.cast_nonneg n) (by linarith : (n : ℝ) ≤ n + 1))
    push_cast
    rw [← hadd, integral_piece hw n]
    ring

/-- `GammaSeq` as an exponential of a sum of logarithms. -/
theorem GammaSeq_eq_exp {w : ℂ} (hw : w ∈ slitPlane) {n : ℕ} (hn : n ≠ 0) :
    GammaSeq w n = exp (w * (Real.log n : ℂ) + (Real.log n.factorial : ℂ) -
      ∑ j ∈ Finset.range (n + 1), log (w + j)) := by
  rw [GammaSeq, exp_sub, exp_add, exp_sum]
  have h1 : exp (w * (Real.log n : ℂ)) = (n : ℂ) ^ w := by
    rw [cpow_def_of_ne_zero (by exact_mod_cast hn), natCast_log, mul_comm]
  have h2 : exp (Real.log n.factorial : ℂ) = (n.factorial : ℂ) := by
    rw [natCast_log, exp_log (by exact_mod_cast (Nat.factorial_pos n).ne')]
  have h3 : ∏ j ∈ Finset.range (n + 1), exp (log (w + j)) = ∏ j ∈ Finset.range (n + 1), (w + j) :=
    Finset.prod_congr rfl (fun j _ => exp_log (natCast_add_ne_zero hw j))
  rw [h1, h2, h3]

/-- Stirling's formula for `n!` in logarithmic form. -/
lemma tendsto_log_factorial :
    Tendsto (fun n : ℕ => Real.log n.factorial - (n + 1 / 2) * Real.log n + n) atTop
      (𝓝 (1 / 2 * Real.log (2 * Real.pi))) := by
  have h := (Stirling.tendsto_stirlingSeq_sqrt_pi).log (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have heq : ∀ n : ℕ, n ≠ 0 → Real.log (Stirling.stirlingSeq n) + 1 / 2 * Real.log 2 =
      Real.log n.factorial - (n + 1 / 2) * Real.log n + n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Stirling.log_stirlingSeq_formula, Real.log_mul (by norm_num) hn'.ne',
      Real.log_div hn'.ne' (Real.exp_pos 1).ne', Real.log_exp]
    ring
  have hlim : 1 / 2 * Real.log (2 * Real.pi) = Real.log √Real.pi + 1 / 2 * Real.log 2 := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_pos.ne']; ring
  rw [hlim]
  refine (h.add_const _).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn using heq n hn

/-- `(w + n + 1/2)(log(w+n) - log n) → w`. -/
lemma tendsto_correction {w : ℂ} (hw : w ∈ slitPlane) :
    Tendsto (fun n : ℕ => (w + n + 1 / 2) * (log (w + n) - (Real.log n : ℂ))) atTop (𝓝 w) := by
  have hz : Tendsto (fun n : ℕ => w / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat w
  have hlog : Tendsto (fun n : ℕ => log (1 + w / n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 + w / n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℂ))).add hz
    have := ((continuousAt_clog one_mem_slitPlane).tendsto).comp h1
    rw [log_one] at this
    exact this
  -- `n log(1 + w/n) → w`
  have hmain : Tendsto (fun n : ℕ => (n : ℂ) * log (1 + w / n)) atTop (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun n : ℕ => ‖w‖ ^ 2 / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hb
    have hev : ∀ᶠ n : ℕ in atTop, 2 * ‖w‖ ≤ n ∧ n ≠ 0 :=
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop (2 * ‖w‖)).and (eventually_ne_atTop 0)
    filter_upwards [hev] with n ⟨hn, hn0⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hzn : ‖w / n‖ = ‖w‖ / n := by
      rw [norm_div, Complex.norm_natCast]
    have hz2 : ‖w / n‖ ≤ 1 / 2 := by
      rw [hzn, div_le_iff₀ hn']; linarith
    have hbound := norm_log_one_add_sub_self_le (z := w / n) (by linarith)
    have hinv : (1 - ‖w / n‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    have hw_eq : (n : ℂ) * log (1 + w / n) - w = (n : ℂ) * (log (1 + w / n) - w / n) := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
      field_simp
    rw [hw_eq, norm_mul, Complex.norm_natCast]
    calc (n : ℝ) * ‖log (1 + w / n) - w / n‖ ≤ n * (‖w / n‖ ^ 2 * (1 - ‖w / n‖)⁻¹ / 2) :=
          mul_le_mul_of_nonneg_left hbound hn'.le
      _ ≤ n * (‖w / n‖ ^ 2 * 2 / 2) := by
          gcongr
      _ = ‖w‖ ^ 2 / n := by rw [hzn]; field_simp
  have hsum := hmain.add ((tendsto_const_nhds (x := w + 1 / 2)).mul hlog)
  rw [mul_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h1 : (1 : ℂ) + w / n ≠ 0 := by
    intro h
    apply natCast_add_ne_zero hw n
    have : (n : ℂ) * (1 + w / n) = w + n := by field_simp; ring
    rw [← this, h, mul_zero]
  have hl : log (w + n) = (Real.log n : ℂ) + log (1 + w / n) := by
    rw [← log_ofReal_mul hn' h1]
    congr 1
    push_cast
    field_simp
    ring
  rw [hl]
  ring

/-- `∫_0^n → J`. -/
lemma tendsto_integral_J {w : ℂ} (hw : w ∈ slitPlane) :
    Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..n, (kerQ t : ℂ) / ((t : ℂ) + w) ^ 2) atTop (𝓝 (J w)) := by
  obtain ⟨s, hs, hsb⟩ := exists_sectorBound hw
  have hint := integrable_Jm hs (slitPlane_ne_zero hw) hsb (le_refl 2)
  exact (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id).comp
    tendsto_natCast_atTop_atTop

/-- The Euler-limit logarithms converge to `logGammaS`. -/
theorem tendsto_logGammaSeq {w : ℂ} (hw : w ∈ slitPlane) :
    Tendsto (fun n : ℕ => w * (Real.log n : ℂ) + (Real.log n.factorial : ℂ) -
      ∑ j ∈ Finset.range (n + 1), log (w + j)) atTop (𝓝 (logGammaS w)) := by
  have hS := (continuous_ofReal.tendsto _).comp tendsto_log_factorial
  have hlim := ((tendsto_const_nhds (x := (w - 1 / 2) * log w)).add hS).sub
    (tendsto_correction hw) |>.add (tendsto_integral_J hw)
  have hval : (w - 1 / 2) * log w + ((1 / 2 * Real.log (2 * Real.pi) : ℝ) : ℂ) - w + J w =
      logGammaS w := by
    unfold logGammaS; push_cast; ring
  rw [hval] at hlim
  refine hlim.congr' (Eventually.of_forall (fun n => ?_))
  simp only [Function.comp_apply]
  rw [sum_log_eq hw n]
  push_cast
  ring

/-- **`exp ∘ logGammaS = Γ` on the slit plane.** -/
theorem exp_logGammaS {w : ℂ} (hw : w ∈ slitPlane) : exp (logGammaS w) = Gamma w := by
  have h1 := ((continuous_exp.tendsto _).comp (tendsto_logGammaSeq hw))
  have h2 := GammaSeq_tendsto_Gamma w
  refine tendsto_nhds_unique (h1.congr' ?_) h2
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (GammaSeq_eq_exp hw hn).symm

end ZetaIrr.Stirling
