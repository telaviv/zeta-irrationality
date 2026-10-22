/-
# Nonvanishing from an oscillating asymptotic (PROOF_BETA §6.6(ii), PROOF_BETA100 §6.6(ii))

The last step of Lemma 6(ii). Suppose that along an arithmetic progression `n_m = n_0 + q m`

    L_m = c_m · (A · sin(n_m θ + φ) + ε_m),      A > 0,  c_m ≠ 0,  ε_m → 0,

and `sin(q θ) ≠ 0`. Then `L_m ≠ 0` for infinitely many `m`. The key inequality is
`|sin u| + |sin(u + v)| ≥ |sin v|` (`abs_sin_le_abs_sin_add_abs_sin_add`).

The complex form `frequently_ne_zero_of_im_asymptotic` takes the hypothesis
`L_m = c_m · (Im(C₀ e^{n_m Ω}) + ε_m e^{n_m Re Ω})` with `C₀ ≠ 0`,
which is the shape (6.6.1) delivers.

Status: complete (no `sorry`).
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Field

namespace ZetaIrr.Analytic

open Filter Topology

/-- `|sin v| ≤ |sin u| + |sin (u + v)|` for all real `u, v`. -/
lemma abs_sin_le_abs_sin_add_abs_sin_add (u v : ℝ) :
    |Real.sin v| ≤ |Real.sin u| + |Real.sin (u + v)| := by
  have h : Real.sin v = Real.sin (u + v) * Real.cos u - Real.cos (u + v) * Real.sin u := by
    rw [← Real.sin_sub]; ring_nf
  rw [h]
  have h1 := Real.abs_cos_le_one u
  have h2 := Real.abs_cos_le_one (u + v)
  calc |Real.sin (u + v) * Real.cos u - Real.cos (u + v) * Real.sin u|
      ≤ |Real.sin (u + v) * Real.cos u| + |Real.cos (u + v) * Real.sin u| := abs_sub _ _
    _ = |Real.sin (u + v)| * |Real.cos u| + |Real.cos (u + v)| * |Real.sin u| := by
        rw [abs_mul, abs_mul]
    _ ≤ |Real.sin (u + v)| * 1 + 1 * |Real.sin u| := by
        gcongr
    _ = |Real.sin u| + |Real.sin (u + v)| := by ring

/-- **Nonvanishing from a sine asymptotic.** If `L m = c m * (A sin(n m θ + φ) + ε m)` eventually,
with `A > 0`, `c m ≠ 0` eventually, `ε m → 0`, `n (m+1) = n m + q` and `sin (q θ) ≠ 0`, then
`L m ≠ 0` for infinitely many `m`. -/
theorem frequently_ne_zero_of_sin_asymptotic (L c ε n : ℕ → ℝ) (A q θ φ : ℝ)
    (hA : 0 < A) (hq : Real.sin (q * θ) ≠ 0) (hn : ∀ m, n (m + 1) = n m + q)
    (hc : ∀ᶠ m in atTop, c m ≠ 0) (hε : Tendsto ε atTop (𝓝 0))
    (hL : ∀ᶠ m in atTop, L m = c m * (A * Real.sin (n m * θ + φ) + ε m)) :
    ∃ᶠ m in atTop, L m ≠ 0 := by
  unfold Filter.Frequently
  intro hzero
  -- eventually `|sin(n m θ + φ)| ≤ |ε m| / A`
  have hsmall : ∀ᶠ m in atTop, A * |Real.sin (n m * θ + φ)| = |ε m| := by
    filter_upwards [hzero, hc, hL] with m h0 hcm hLm
    rw [hLm] at h0
    rcases mul_eq_zero.1 (not_not.1 h0) with h | h
    · exact absurd h hcm
    · have : A * Real.sin (n m * θ + φ) = -ε m := by linarith
      rw [← abs_of_pos hA, ← abs_mul, this, abs_neg]
  have hsmall' : ∀ᶠ m in atTop, A * |Real.sin (n (m + 1) * θ + φ)| = |ε (m + 1)| :=
    (tendsto_add_atTop_nat 1).eventually hsmall
  -- hence `A |sin(qθ)| ≤ |ε m| + |ε (m+1)|` eventually
  have hbound : ∀ᶠ m in atTop, A * |Real.sin (q * θ)| ≤ |ε m| + |ε (m + 1)| := by
    filter_upwards [hsmall, hsmall'] with m h1 h2
    have key := abs_sin_le_abs_sin_add_abs_sin_add (n m * θ + φ) (q * θ)
    have e : n m * θ + φ + q * θ = n (m + 1) * θ + φ := by rw [hn]; ring
    rw [e] at key
    calc A * |Real.sin (q * θ)| ≤ A * (|Real.sin (n m * θ + φ)| + |Real.sin (n (m + 1) * θ + φ)|) :=
          mul_le_mul_of_nonneg_left key hA.le
      _ = |ε m| + |ε (m + 1)| := by rw [mul_add, h1, h2]
  have hlim : Tendsto (fun m => |ε m| + |ε (m + 1)|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => |ε m|) atTop (𝓝 0) := by simpa using hε.abs
    have h2 : Tendsto (fun m => |ε (m + 1)|) atTop (𝓝 0) := h1.comp (tendsto_add_atTop_nat 1)
    simpa using h1.add h2
  have hpos : 0 < A * |Real.sin (q * θ)| := mul_pos hA (abs_pos.2 hq)
  have hev := hlim.eventually (gt_mem_nhds hpos)
  obtain ⟨m, hm1, hm2⟩ := (hbound.and hev).exists
  linarith

/-- `Im (C₀ e^{w}) = |C₀| e^{Re w} sin(Im w + arg C₀)` for `C₀ ≠ 0`. -/
lemma im_mul_exp_eq (C₀ w : ℂ) (hC : C₀ ≠ 0) :
    (C₀ * Complex.exp w).im = ‖C₀‖ * Real.exp w.re * Real.sin (w.im + Complex.arg C₀) := by
  have h : C₀ * Complex.exp w = Complex.exp (Complex.log C₀ + w) := by
    rw [Complex.exp_add, Complex.exp_log hC]
  rw [h, Complex.exp_im, Complex.add_re, Complex.add_im, Complex.log_re, Complex.log_im,
    Real.exp_add, Real.exp_log (norm_pos_iff.2 hC)]
  ring_nf

/-- **Nonvanishing, complex form** (the shape of PROOF_BETA100 (6.6.1)). If eventually
`L m = c m * (Im (C₀ e^{n_m Ω}) + ε m · e^{n_m Re Ω})` with `c m ≠ 0`, `C₀ ≠ 0`, `ε m → 0`,
`n (m+1) = n m + q` and `sin (q Im Ω) ≠ 0`, then `L m ≠ 0` for infinitely many `m`. -/
theorem frequently_ne_zero_of_im_asymptotic (L c ε n : ℕ → ℝ) (C₀ Ω : ℂ) (q : ℝ)
    (hC : C₀ ≠ 0) (hq : Real.sin (q * Ω.im) ≠ 0) (hn : ∀ m, n (m + 1) = n m + q)
    (hc : ∀ᶠ m in atTop, c m ≠ 0) (hε : Tendsto ε atTop (𝓝 0))
    (hL : ∀ᶠ m in atTop,
      L m = c m * ((C₀ * Complex.exp (n m * Ω)).im + ε m * Real.exp (n m * Ω.re))) :
    ∃ᶠ m in atTop, L m ≠ 0 := by
  refine frequently_ne_zero_of_sin_asymptotic L (fun m => c m * Real.exp (n m * Ω.re))
    (fun m => ε m) n ‖C₀‖ q Ω.im (Complex.arg C₀) (norm_pos_iff.2 hC) hq hn ?_ hε ?_
  · filter_upwards [hc] with m hm
    exact mul_ne_zero hm (Real.exp_pos _).ne'
  · filter_upwards [hL] with m hm
    rw [hm, im_mul_exp_eq _ _ hC]
    have h1 : ((n m : ℂ) * Ω).re = n m * Ω.re := by simp
    have h2 : ((n m : ℂ) * Ω).im = n m * Ω.im := by simp
    rw [h1, h2]
    ring

end ZetaIrr.Analytic
