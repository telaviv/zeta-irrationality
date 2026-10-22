/-
# Laplace's method for a complex phase on a short segment (Lemma 6, the disc part)

Abstract form of the disc estimate. Parametrise the steepest-descent segment through the saddle as
`s ↦ x₀ + s d`, `|s| ≤ ρ`, and write the phase as

    n f(x₀ + s d) = n f(x₀) + n φ(s),      φ(s) = -K s²/2 + T(s),     |T(s)| ≤ M |s|³/6,

with `K > 0` and `M ρ ≤ 3K/2` (the condition `ρ ≤ 3K/(2M)` of (S1)). For an amplitude `a` with
`|a| ≤ A₀` and `|a(s) - a(0)| ≤ A₁ |s|`,

    | ∫_{-ρ}^{ρ} e^{n φ(s)} a(s) ds - a(0) √(2π/(nK)) |
        ≤ (16√(2π)/3 · A₀ M / K² + 2√(2π) A₁ / K) / n + A₀ e^{-nKρ²/4} √(4π/(nK)).

This is `laplace_bound`. The proof combines
* `|e^{nT} - 1| ≤ n|T| e^{n|T|}` and `n|T| ≤ nK s²/4` (from `Mρ ≤ 3K/2`);
* `|a(s) - a(0)| ≤ A₁|s|`;
* the Gaussian tail outside `[-ρ, ρ]`;
each bounded by an explicit Gaussian integral (`integral_gaussian`).

`taylor_phase_bound` derives the hypothesis `|T(s)| ≤ M|s|³/6` from complex differentiability of
the phase `F` along the segment with `F'(x₀) = 0`, `F''(x₀) d² = -K`, `|F'''| ≤ M`, `|d| = 1`.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ZetaIrr.Analytic

open Real Set MeasureTheory Filter

/-- `‖e^z - 1‖ ≤ ‖z‖ e^{‖z‖}`. -/
lemma norm_cexp_sub_one_le_mul_exp (z : ℂ) : ‖Complex.exp z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t : ℝ => Complex.exp (t * z))
      (Complex.exp (t * z) * z) (Icc 0 1) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z t := by
      simpa using (hasDerivAt_id t).ofReal_comp.mul_const z
    exact h1.cexp.hasDerivWithinAt
  have hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖Complex.exp (t * z) * z‖ ≤ Real.exp ‖z‖ * ‖z‖ := by
    intro t ht
    rw [norm_mul]
    gcongr
    calc ‖Complex.exp (t * z)‖ ≤ Real.exp ‖(t : ℂ) * z‖ := Complex.norm_exp_le_exp_norm _
      _ ≤ Real.exp ‖z‖ := by
        gcongr
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
  have := norm_image_sub_le_of_norm_deriv_le_segment' hd hb 1 (right_mem_Icc.2 zero_le_one)
  simpa [mul_comm] using this

/-- `|s| √b ≤ e^{b s²/2}`. -/
lemma abs_mul_sqrt_le_exp (b s : ℝ) (hb : 0 < b) : |s| * √b ≤ Real.exp (b * s ^ 2 / 2) := by
  have hu2 : (|s| * √b) ^ 2 = b * s ^ 2 := by
    rw [mul_pow, sq_abs, Real.sq_sqrt hb.le]; ring
  have := Real.add_one_le_exp (b * s ^ 2 / 2)
  nlinarith [sq_nonneg (|s| * √b - 1)]

/-- `|s|³ b √b ≤ 2 e^{b s²/2}`. -/
lemma abs_pow_three_mul_le_exp (b s : ℝ) (hb : 0 < b) :
    |s| ^ 3 * (b * √b) ≤ 2 * Real.exp (b * s ^ 2 / 2) := by
  set u := |s| * √b with hu
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ^ 2 = b * s ^ 2 := by
    rw [hu, mul_pow, sq_abs, Real.sq_sqrt hb.le]; ring
  have hcube : |s| ^ 3 * (b * √b) = u ^ 3 := by
    rw [hu, mul_pow]
    have : √b ^ 3 = √b ^ 2 * √b := by ring
    rw [this, Real.sq_sqrt hb.le]
  have hq := Real.quadratic_le_exp_of_nonneg (x := b * s ^ 2 / 2) (by positivity)
  rw [hcube]
  have h4 : u ^ 4 = (b * s ^ 2) ^ 2 := by rw [← hu2]; ring
  nlinarith [sq_nonneg (u ^ 2 / 2 - u)]

/-- The Gaussian integral in the form used below. -/
lemma integral_gaussian' (c : ℝ) : ∫ s : ℝ, Real.exp (-c * s ^ 2) = √(π / c) :=
  integral_gaussian c

/-- **Laplace's method on a segment, explicit error.** See the module docstring. -/
theorem laplace_bound {n K M ρ A₀ A₁ : ℝ} (hn : 0 < n) (hK : 0 < K) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hρM : M * ρ ≤ 3 * K / 2) {φ a : ℝ → ℂ}
    (hφc : ContinuousOn φ (Icc (-ρ) ρ)) (hac : ContinuousOn a (Icc (-ρ) ρ))
    (hT : ∀ s ∈ Icc (-ρ) ρ, ‖φ s + K * s ^ 2 / 2‖ ≤ M * |s| ^ 3 / 6)
    (ha0 : ∀ s ∈ Icc (-ρ) ρ, ‖a s‖ ≤ A₀)
    (ha1 : ∀ s ∈ Icc (-ρ) ρ, ‖a s - a 0‖ ≤ A₁ * |s|) :
    ‖(∫ s in (-ρ)..ρ, Complex.exp (n * φ s) * a s) - a 0 * ((√(2 * π / (n * K)) : ℝ) : ℂ)‖ ≤
      (16 * √(2 * π) / 3 * A₀ * M / K ^ 2 + 2 * √(2 * π) * A₁ / K) / n
        + A₀ * Real.exp (-(n * K * ρ ^ 2 / 4)) * √(4 * π / (n * K)) := by
  have hρ0 : (0 : ℝ) ∈ Icc (-ρ) ρ := ⟨by linarith, hρ.le⟩
  have hA₀ : 0 ≤ A₀ := (norm_nonneg _).trans (ha0 0 hρ0)
  have hA₁ : 0 ≤ A₁ := by
    have h := ha1 ρ (right_mem_Icc.2 (by linarith))
    have : 0 ≤ A₁ * |ρ| := (norm_nonneg _).trans h
    rw [abs_of_pos hρ] at this
    exact nonneg_of_mul_nonneg_left this hρ
  set b := n * K / 4 with hb_def
  set b2 := n * K / 2 with hb2_def
  have hb : 0 < b := by positivity
  have hb2 : 0 < b2 := by positivity
  set g : ℝ → ℝ := fun s => Real.exp (-b2 * s ^ 2) with hg_def
  set h : ℝ → ℂ := fun s => Complex.exp (n * φ s) * a s with hh_def
  set c1 := A₀ * (n * M / 6) * (2 / (b * √b)) with hc1
  set c2 := A₁ / √b2 with hc2
  set c3 := A₀ * Real.exp (-(n * K * ρ ^ 2 / 4)) with hc3
  set P : ℝ → ℝ := fun s => c1 * Real.exp (-(b / 2) * s ^ 2) + c2 * Real.exp (-(b2 / 2) * s ^ 2)
    + c3 * Real.exp (-b * s ^ 2) with hP_def
  have hc1n : 0 ≤ c1 := by positivity
  have hc2n : 0 ≤ c2 := by positivity
  have hc3n : 0 ≤ c3 := by positivity
  -- integrability
  have hg_int : Integrable g := integrable_exp_neg_mul_sq hb2
  have hgC_int : Integrable (fun s => a 0 * ((g s : ℝ) : ℂ)) :=
    (hg_int.ofReal (𝕜 := ℂ)).const_mul _
  have hh_cont : ContinuousOn h (Icc (-ρ) ρ) := by
    refine ContinuousOn.mul ?_ hac
    exact (continuousOn_const.mul hφc).cexp
  have hh_int : Integrable ((Ioc (-ρ) ρ).indicator h) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact (hh_cont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hP_int : Integrable P := by
    refine ((Integrable.const_mul (integrable_exp_neg_mul_sq (by positivity)) c1).add
      (Integrable.const_mul (integrable_exp_neg_mul_sq (by positivity)) c2)).add
      (Integrable.const_mul (integrable_exp_neg_mul_sq hb) c3)
  -- the Gaussian integral of `g`
  have hgint : ∫ s, g s = √(2 * π / (n * K)) := by
    rw [hg_def, integral_gaussian']
    congr 1
    rw [hb2_def]; field_simp
  -- rewrite the left side as one integral over `ℝ`
  have hLHS : (∫ s in (-ρ)..ρ, h s) - a 0 * ((√(2 * π / (n * K)) : ℝ) : ℂ)
      = ∫ s, ((Ioc (-ρ) ρ).indicator h s - a 0 * ((g s : ℝ) : ℂ)) := by
    rw [integral_sub hh_int hgC_int, intervalIntegral.integral_of_le (by linarith),
      ← integral_indicator measurableSet_Ioc, integral_const_mul, integral_complex_ofReal, hgint]
  -- pointwise bound
  have hpt : ∀ s, ‖(Ioc (-ρ) ρ).indicator h s - a 0 * ((g s : ℝ) : ℂ)‖ ≤ P s := by
    intro s
    have hgs : 0 < g s := Real.exp_pos _
    by_cases hs : s ∈ Ioc (-ρ) ρ
    · rw [indicator_of_mem hs]
      have hsI : s ∈ Icc (-ρ) ρ := Ioc_subset_Icc_self hs
      have habs : |s| ≤ ρ := abs_le.2 ⟨hs.1.le, hs.2⟩
      set T : ℂ := φ s + K * s ^ 2 / 2 with hT_def
      have hTb := hT s hsI
      -- `n φ = -b2 s² + n T`
      have hsplit : Complex.exp (n * φ s) = ((g s : ℝ) : ℂ) * Complex.exp (n * T) := by
        rw [hg_def, Complex.ofReal_exp, ← Complex.exp_add]
        congr 1
        rw [hT_def, hb2_def]; push_cast; ring
      have hnT1 : ‖(n : ℂ) * T‖ ≤ n * (M * |s| ^ 3 / 6) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
        exact mul_le_mul_of_nonneg_left hTb hn.le
      have hnT2 : ‖(n : ℂ) * T‖ ≤ b * s ^ 2 := by
        refine hnT1.trans ?_
        have : M * |s| ≤ 3 * K / 2 := (mul_le_mul_of_nonneg_left habs hM).trans hρM
        have hs3 : |s| ^ 3 = |s| * s ^ 2 := by rw [← sq_abs s]; ring
        rw [hb_def, hs3]
        have := mul_le_mul_of_nonneg_right this (sq_nonneg s)
        nlinarith
      -- term I
      have hI : ‖(Complex.exp (n * φ s) - ((g s : ℝ) : ℂ)) * a s‖
          ≤ c1 * Real.exp (-(b / 2) * s ^ 2) := by
        rw [hsplit, ← mul_sub_one, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hgs]
        have he := norm_cexp_sub_one_le_mul_exp ((n : ℂ) * T)
        have he' : ‖Complex.exp (n * T) - 1‖ ≤ n * (M * |s| ^ 3 / 6) * Real.exp (b * s ^ 2) :=
          he.trans (mul_le_mul hnT1 (Real.exp_le_exp.2 hnT2) (Real.exp_pos _).le
            (by positivity))
        have hcube := abs_pow_three_mul_le_exp b s hb
        have hbsb : 0 < b * √b := by positivity
        have hcube' : |s| ^ 3 ≤ 2 / (b * √b) * Real.exp (b * s ^ 2 / 2) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hbsb]; linarith
        have hexp : g s * Real.exp (b * s ^ 2) * Real.exp (b * s ^ 2 / 2)
            = Real.exp (-(b / 2) * s ^ 2) := by
          rw [hg_def, ← Real.exp_add, ← Real.exp_add, hb2_def, hb_def]; congr 1; ring
        calc g s * ‖Complex.exp (n * T) - 1‖ * ‖a s‖
            ≤ g s * (n * (M * |s| ^ 3 / 6) * Real.exp (b * s ^ 2)) * A₀ := by
              gcongr
              exact ha0 s hsI
          _ = A₀ * (n * M / 6) * |s| ^ 3 * (g s * Real.exp (b * s ^ 2)) := by ring
          _ ≤ A₀ * (n * M / 6) * (2 / (b * √b) * Real.exp (b * s ^ 2 / 2))
                * (g s * Real.exp (b * s ^ 2)) := by gcongr
          _ = c1 * Real.exp (-(b / 2) * s ^ 2) := by rw [hc1, ← hexp]; ring
      -- term II
      have hII : ‖((g s : ℝ) : ℂ) * (a s - a 0)‖ ≤ c2 * Real.exp (-(b2 / 2) * s ^ 2) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgs]
        have h1 := abs_mul_sqrt_le_exp b2 s hb2
        have hsb : 0 < √b2 := Real.sqrt_pos.2 hb2
        have h1' : |s| ≤ 1 / √b2 * Real.exp (b2 * s ^ 2 / 2) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hsb]; linarith
        have hexp : g s * Real.exp (b2 * s ^ 2 / 2) = Real.exp (-(b2 / 2) * s ^ 2) := by
          rw [hg_def, ← Real.exp_add]; congr 1; ring
        calc g s * ‖a s - a 0‖ ≤ g s * (A₁ * |s|) := by gcongr; exact ha1 s hsI
          _ ≤ g s * (A₁ * (1 / √b2 * Real.exp (b2 * s ^ 2 / 2))) := by gcongr
          _ = c2 * Real.exp (-(b2 / 2) * s ^ 2) := by rw [hc2, ← hexp]; ring
      have hsum : h s - a 0 * ((g s : ℝ) : ℂ)
          = (Complex.exp (n * φ s) - ((g s : ℝ) : ℂ)) * a s + ((g s : ℝ) : ℂ) * (a s - a 0) := by
        rw [hh_def]; ring
      rw [hsum]
      calc _ ≤ ‖(Complex.exp (n * φ s) - ((g s : ℝ) : ℂ)) * a s‖
            + ‖((g s : ℝ) : ℂ) * (a s - a 0)‖ := norm_add_le _ _
        _ ≤ c1 * Real.exp (-(b / 2) * s ^ 2) + c2 * Real.exp (-(b2 / 2) * s ^ 2) :=
            add_le_add hI hII
        _ ≤ P s := by
          rw [hP_def]
          have : 0 ≤ c3 * Real.exp (-b * s ^ 2) := by positivity
          linarith
    · rw [indicator_of_notMem hs, zero_sub, norm_neg, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hgs]
      have hsq : ρ ^ 2 ≤ s ^ 2 := by
        rw [mem_Ioc, not_and_or, not_lt, not_le] at hs
        rcases hs with h1 | h1
        · nlinarith
        · nlinarith
      have hgle : g s ≤ Real.exp (-(n * K * ρ ^ 2 / 4)) * Real.exp (-b * s ^ 2) := by
        rw [hg_def, ← Real.exp_add, Real.exp_le_exp, hb2_def, hb_def]
        have : 0 ≤ n * K := by positivity
        nlinarith
      calc ‖a 0‖ * g s ≤ A₀ * (Real.exp (-(n * K * ρ ^ 2 / 4)) * Real.exp (-b * s ^ 2)) :=
            mul_le_mul (ha0 0 hρ0) hgle hgs.le hA₀
        _ = c3 * Real.exp (-b * s ^ 2) := by rw [hc3]; ring
        _ ≤ P s := by
          rw [hP_def]
          have : 0 ≤ c1 * Real.exp (-(b / 2) * s ^ 2) := by positivity
          have : 0 ≤ c2 * Real.exp (-(b2 / 2) * s ^ 2) := by positivity
          linarith
  -- integrate the bound
  have I1 : Integrable (fun s : ℝ => c1 * Real.exp (-(b / 2) * s ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul c1
  have I2 : Integrable (fun s : ℝ => c2 * Real.exp (-(b2 / 2) * s ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul c2
  have I3 : Integrable (fun s : ℝ => c3 * Real.exp (-b * s ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul c3
  have hPint : ∫ s, P s = c1 * √(π / (b / 2)) + c2 * √(π / (b2 / 2)) + c3 * √(π / b) := by
    have I12 : Integrable (fun s : ℝ => c1 * Real.exp (-(b / 2) * s ^ 2)
        + c2 * Real.exp (-(b2 / 2) * s ^ 2)) := I1.add I2
    rw [hP_def, integral_add I12 I3, integral_add I1 I2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_gaussian',
      integral_gaussian', integral_gaussian']
  rw [hh_def] at hLHS
  rw [hLHS]
  refine (norm_integral_le_of_norm_le hP_int (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [hPint]
  -- algebra with square roots
  have hsb : 0 < √b := Real.sqrt_pos.2 hb
  have hsb2 : 0 < √b2 := Real.sqrt_pos.2 hb2
  have e1 : √(π / (b / 2)) = √(2 * π) / √b := by
    rw [← Real.sqrt_div (by positivity)]; congr 1; field_simp
  have e2 : √(π / (b2 / 2)) = √(2 * π) / √b2 := by
    rw [← Real.sqrt_div (by positivity)]; congr 1; field_simp
  have e3 : √(π / b) = √(4 * π / (n * K)) := by
    congr 1; rw [hb_def]; field_simp
  have hbb : √b * √b = b := Real.mul_self_sqrt hb.le
  have hbb2 : √b2 * √b2 = b2 := Real.mul_self_sqrt hb2.le
  rw [e1, e2, e3]
  have t1 : c1 * (√(2 * π) / √b) = A₀ * n * M * √(2 * π) / (3 * b * (√b * √b)) := by
    rw [hc1]; field_simp; ring
  have t2 : c2 * (√(2 * π) / √b2) = A₁ * √(2 * π) / (√b2 * √b2) := by
    rw [hc2]; field_simp
  rw [t1, t2, hbb, hbb2, hb_def, hb2_def]
  field_simp
  ring

/-! ### Taylor bound for the phase along the segment -/

/-- Fencing on `[0,1]` from a zero initial value (a form of
`image_norm_le_of_norm_deriv_right_le_deriv_boundary`). -/
lemma norm_le_of_deriv_bound {g g' : ℝ → ℂ} {B B' : ℝ → ℝ}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' t) t) (h0 : g 0 = 0)
    (hB : ∀ x, HasDerivAt B (B' x) x) (hB0 : 0 ≤ B 0)
    (bound : ∀ t ∈ Icc (0 : ℝ) 1, ‖g' t‖ ≤ B' t) : ∀ t ∈ Icc (0 : ℝ) 1, ‖g t‖ ≤ B t := by
  intro t ht
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hg x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (by rw [h0, norm_zero]; exact hB0)
    hB (fun x hx => bound x (Ico_subset_Icc_self hx)) ht

/-- **Second-order Taylor bound along a segment.** If `F' = F1`, `F1' = F2`, `F2' = F3` (complex
derivatives) at the points `x₀ + t v`, `t ∈ [0,1]`, and `‖F3‖ ≤ M` there, then
`‖F(x₀ + v) - F x₀ - F1 x₀ v - F2 x₀ v²/2‖ ≤ M ‖v‖³/6`. -/
theorem norm_taylor_two_le {F F1 F2 F3 : ℂ → ℂ} {x₀ v : ℂ} {M : ℝ}
    (h1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F (F1 (x₀ + t * v)) (x₀ + t * v))
    (h2 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F1 (F2 (x₀ + t * v)) (x₀ + t * v))
    (h3 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F2 (F3 (x₀ + t * v)) (x₀ + t * v))
    (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖F3 (x₀ + t * v)‖ ≤ M) :
    ‖F (x₀ + v) - F x₀ - F1 x₀ * v - F2 x₀ * v ^ 2 / 2‖ ≤ M * ‖v‖ ^ 3 / 6 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (left_mem_Icc.2 zero_le_one))
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x₀ + (t : ℂ) * v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const v).const_add x₀
  have hcomp : ∀ {G G' : ℂ → ℂ}, (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt G (G' (x₀ + t * v)) (x₀ + t * v))
      → ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => G (x₀ + t * v)) (G' (x₀ + t * v) * v) t := by
    intro G G' hG t ht
    exact (hG t ht).comp t (hγ t)
  have hlin : ∀ (c : ℂ) (t : ℝ), HasDerivAt (fun t : ℝ => c * ((t : ℂ) * v)) (c * v) t := by
    intro c t
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const v).const_mul c
  have hx0 : x₀ + ((0 : ℝ) : ℂ) * v = x₀ := by simp
  set nv := ‖v‖ with hnv
  -- step 0
  have s0 : ∀ t ∈ Icc (0 : ℝ) 1, ‖F2 (x₀ + t * v) - F2 x₀‖ ≤ M * nv * t := by
    refine norm_le_of_deriv_bound (g' := fun t => F3 (x₀ + t * v) * v) (B' := fun _ => M * nv)
      (fun t ht => (hcomp h3 t ht).sub_const _) (by rw [hx0, sub_self]) ?_ (by simp) ?_
    · intro x; simpa using (hasDerivAt_id x).const_mul (M * nv)
    · intro t ht; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _)
  -- step 1
  have s1 : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖F1 (x₀ + t * v) - F1 x₀ - F2 x₀ * (t * v)‖ ≤ M * nv ^ 2 * t ^ 2 / 2 := by
    refine norm_le_of_deriv_bound
      (g' := fun t => (F2 (x₀ + t * v) - F2 x₀) * v) (B' := fun t => M * nv ^ 2 * t)
      (fun t ht => by
        have := ((hcomp h2 t ht).sub_const (F1 x₀)).sub (hlin (F2 x₀) t)
        convert this using 1; ring) (by simp) ?_ (by simp) ?_
    · intro x
      have := ((hasDerivAt_pow 2 x).const_mul (M * nv ^ 2)).div_const 2
      convert this using 1; norm_num; ring
    · intro t ht
      rw [norm_mul]
      calc ‖F2 (x₀ + t * v) - F2 x₀‖ * ‖v‖ ≤ M * nv * t * nv :=
            mul_le_mul_of_nonneg_right (s0 t ht) (norm_nonneg _)
        _ = M * nv ^ 2 * t := by ring
  -- step 2
  have s2 : ∀ t ∈ Icc (0 : ℝ) 1, ‖F (x₀ + t * v) - F x₀ - F1 x₀ * (t * v)
      - F2 x₀ * (t * v) ^ 2 / 2‖ ≤ M * nv ^ 3 * t ^ 3 / 6 := by
    refine norm_le_of_deriv_bound
      (g' := fun t => (F1 (x₀ + t * v) - F1 x₀ - F2 x₀ * (t * v)) * v)
      (B' := fun t => M * nv ^ 3 * t ^ 2 / 2)
      (fun t ht => by
        have hq : HasDerivAt (fun t : ℝ => F2 x₀ * ((t : ℂ) * v) ^ 2 / 2)
            (F2 x₀ * (2 * ((t : ℂ) * v) * v) / 2) t := by
          have := ((((hasDerivAt_id t).ofReal_comp.mul_const v).pow 2).const_mul
            (F2 x₀)).div_const 2
          simpa using this
        have := (((hcomp h1 t ht).sub_const (F x₀)).sub (hlin (F1 x₀) t)).sub hq
        convert this using 1; ring) (by simp) ?_ (by simp) ?_
    · intro x
      have := ((hasDerivAt_pow 3 x).const_mul (M * nv ^ 3)).div_const 6
      convert this using 1; norm_num; ring
    · intro t ht
      rw [norm_mul]
      calc ‖F1 (x₀ + t * v) - F1 x₀ - F2 x₀ * (t * v)‖ * ‖v‖ ≤ M * nv ^ 2 * t ^ 2 / 2 * nv :=
            mul_le_mul_of_nonneg_right (s1 t ht) (norm_nonneg _)
        _ = M * nv ^ 3 * t ^ 2 / 2 := by ring
  have := s2 1 (right_mem_Icc.2 zero_le_one)
  simpa using this

/-- **The (S1) Taylor hypothesis from derivative data.** If the phase `F` has complex derivatives
`F1, F2, F3` along the segment `x₀ + s d`, `|s| ≤ ρ`, with `F1 x₀ = 0`, `F2 x₀ · d² = -K`, `‖d‖ = 1`
and `‖F3‖ ≤ M` on the segment, then `φ(s) := F(x₀ + s d) - F(x₀)` satisfies the hypothesis
`‖φ(s) + K s²/2‖ ≤ M |s|³/6` of `laplace_bound`. -/
theorem taylor_phase_bound {F F1 F2 F3 : ℂ → ℂ} {x₀ d : ℂ} {K M ρ : ℝ} (hd : ‖d‖ = 1)
    (hF1 : F1 x₀ = 0) (hF2 : F2 x₀ * d ^ 2 = -K)
    (h1 : ∀ s ∈ Icc (-ρ) ρ, HasDerivAt F (F1 (x₀ + s * d)) (x₀ + s * d))
    (h2 : ∀ s ∈ Icc (-ρ) ρ, HasDerivAt F1 (F2 (x₀ + s * d)) (x₀ + s * d))
    (h3 : ∀ s ∈ Icc (-ρ) ρ, HasDerivAt F2 (F3 (x₀ + s * d)) (x₀ + s * d))
    (hM : ∀ s ∈ Icc (-ρ) ρ, ‖F3 (x₀ + s * d)‖ ≤ M) :
    ∀ s ∈ Icc (-ρ) ρ, ‖(F (x₀ + s * d) - F x₀) + K * s ^ 2 / 2‖ ≤ M * |s| ^ 3 / 6 := by
  intro s hs
  have hts : ∀ t ∈ Icc (0 : ℝ) 1, t * s ∈ Icc (-ρ) ρ := by
    intro t ht
    have hρ : |s| ≤ ρ := abs_le.2 ⟨hs.1, hs.2⟩
    have : |t * s| ≤ ρ := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans hρ
    exact ⟨(abs_le.1 this).1, (abs_le.1 this).2⟩
  have e : ∀ t : ℝ, x₀ + (t : ℂ) * ((s : ℂ) * d) = x₀ + ((t * s : ℝ) : ℂ) * d := by
    intro t; push_cast; ring
  have key := norm_taylor_two_le (F := F) (F1 := F1) (F2 := F2) (F3 := F3) (x₀ := x₀)
    (v := (s : ℂ) * d) (M := M)
    (fun t ht => by rw [e]; exact h1 _ (hts t ht))
    (fun t ht => by rw [e]; exact h2 _ (hts t ht))
    (fun t ht => by rw [e]; exact h3 _ (hts t ht))
    (fun t ht => by rw [e]; exact hM _ (hts t ht))
  have hv : ‖(s : ℂ) * d‖ = |s| := by
    rw [norm_mul, hd, Complex.norm_real, Real.norm_eq_abs, mul_one]
  rw [hv, hF1, zero_mul, sub_zero] at key
  have : F2 x₀ * ((s : ℂ) * d) ^ 2 / 2 = -((K : ℂ) * s ^ 2 / 2) := by
    rw [mul_pow, ← mul_assoc, mul_comm (F2 x₀), mul_assoc, hF2]; ring
  rw [this, sub_neg_eq_add] at key
  exact key

end ZetaIrr.Analytic
