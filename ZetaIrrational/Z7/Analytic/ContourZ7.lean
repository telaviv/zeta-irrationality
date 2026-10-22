/-
# `L_n` as a contour integral of `G_n = R_n · k⁗` (Lemma 6)

`L_eq_half_line`: for every non-integer `c ∈ (0, 220(m+1) + 1)`,

    Z7.L m = -(1/π) Re ∫_0^∞ G_n(c + iy) dy,      G_n(z) = R_n(z) k₄(z),  k₄ = (π cot(πz))⁗,

i.e. `L_n = -(1/π) Im ∫_c^{c+i∞} G_n(z) dz`. Steps:
1. the contour formula `hasSum_cot_eq_line_integral` for `f = R_n⁗` (its zeros at `1, …, rn`
   cancel the kernel's poles, `RCd_nat_zero`; decay from `RCd_bound`);
2. four integrations by parts on the line (`integral_line_by_parts4`):
   `∫ R_n⁗ k₀ = ∫ R_n k₄`;
3. conjugation symmetry (`integral_eq_two_re_Ioi`).

The integration by parts moves all four derivatives onto the kernel; no boundary term arises.
-/
import ZetaIrrational.Z7.Analytic.Bound
import ZetaIrrational.Analytic.ContourCot
import ZetaIrrational.Analytic.ByParts

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Real MeasureTheory Set Filter Topology
open ZetaIrr.Analytic ZetaIrr.Fam.Analytic

/-- `G_n(z) = R_n(z) k₄(z)`, `k₄ = (π cot(πz))⁗`. -/
noncomputable def Gfn (m : ℕ) (z : ℂ) : ℂ := RC m z * kk 4 z

lemma sin_ne_zero_of_line {c : ℝ} (hcZ : ∀ k : ℤ, c ≠ k) (y : ℝ) :
    Complex.sin (π * ((c : ℂ) + y * I)) ≠ 0 := by
  refine sin_pi_ne_zero_of_re (fun k hk => hcZ k ?_)
  simpa using hk

lemma sin_real_ne_zero {c : ℝ} (hcZ : ∀ k : ℤ, c ≠ k) : Real.sin (π * c) ≠ 0 := by
  intro h0
  rw [Real.sin_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  exact hcZ k (mul_right_cancel₀ Real.pi_ne_zero (by rw [hk]; ring : (k : ℝ) * π = c * π)).symm

/-- On the line `Re z = c`, `‖k_j‖ ≤ 24 π⁵ B⁵` with `B = 1/|sin(πc)|`. -/
lemma norm_kk_line_le {c : ℝ} (hcZ : ∀ k : ℤ, c ≠ k) (j : ℕ) (y : ℝ) :
    ‖kk j ((c : ℂ) + y * I)‖ ≤ 24 * π ^ 5 * (1 / |Real.sin (π * c)|) ^ 5 := by
  have hre : ((c : ℂ) + y * I).re = c := by simp
  have hs := sin_real_ne_zero hcZ
  have h := norm_cotP_cscP_le_of_re (z := (c : ℂ) + y * I) (by rw [hre]; exact hs)
  rw [hre] at h
  have hB : 1 ≤ 1 / |Real.sin (π * c)| := by
    rw [le_div_iff₀ (abs_pos.2 hs), one_mul]; exact Real.abs_sin_le_one _
  exact norm_kk_le j hB h.1 h.2

/-- **`L_n` as a half-line integral.** -/
theorem L_eq_half_line (m : ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 220 * ((m : ℝ) + 1) + 1)
    (hcZ : ∀ k : ℤ, c ≠ k) :
    Z7.L m = -(1 / π) * (∫ y in Ioi (0 : ℝ), Gfn m (c + y * I)).re := by
  have hc' : -1 < c := by linarith
  have hline : ∀ y : ℝ, ((c : ℂ) + y * I) ∉ poles m := fun y =>
    mem_compl_poles_of_re (by simpa using hc')
  -- step 1: the contour formula for `f = R_n⁗`
  obtain ⟨C4, hC4⟩ := RCd_bound m 4 (c := c) hc'
  have hdiff : DifferentiableOn ℂ (RCd m 4) {z : ℂ | -1 / 2 < z.re} := fun z hz =>
    (RCd_differentiableAt m 4 (mem_compl_poles_of_re (by
      simp only [Set.mem_setOf_eq] at hz; linarith))).differentiableWithinAt
  have hz : ∀ t : ℕ, 1 ≤ t → (t : ℝ) < c → RCd m 4 t = 0 := by
    intro t ht1 ht
    apply RCd_nat_zero m t 4 (by norm_num) ht1
    have : (t : ℝ) < ((220 * (m + 1) + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.1 this
    omega
  have hsum := hasSum_cot_eq_line_integral (c₀ := -1 / 2) hdiff hC4 (by linarith) hc0 hcZ hz
  -- step 2: integration by parts
  have hs := sin_real_ne_zero hcZ
  set B : ℝ := 24 * π ^ 5 * (1 / |Real.sin (π * c)|) ^ 5 with hB
  have hkB : ∀ j : ℕ, ∀ y : ℝ, ‖kk j ((c : ℂ) + y * I)‖ ≤ B := fun j y =>
    norm_kk_line_le hcZ j y
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hkB 0 0)
  have hdecay : ∀ j : ℕ, ∃ C : ℝ, ∀ y : ℝ, ‖RCd m j ((c : ℂ) + y * I)‖ ≤ C * (1 + y ^ 2)⁻¹ := by
    intro j
    obtain ⟨C, hC⟩ := RCd_bound m j (c := c) hc'
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC (c : ℂ) (by simp))
      exact nonneg_of_mul_nonneg_left this (by positivity)
    refine ⟨C, fun y => (hC _ (by simp)).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (inv_one_add_norm_sq_le c y) hC0
  have hcontR : ∀ j : ℕ, Continuous (fun y : ℝ => RCd m j ((c : ℂ) + y * I)) := by
    intro j
    rw [continuous_iff_continuousAt]
    intro y
    exact ContinuousAt.comp (g := RCd m j) (RCd_differentiableAt m j (hline y)).continuousAt
      (continuous_line c).continuousAt
  have hcontK : ∀ j : ℕ, Continuous (fun y : ℝ => kk j ((c : ℂ) + y * I)) := by
    intro j
    rw [continuous_iff_continuousAt]
    intro y
    exact ContinuousAt.comp (g := kk j) (differentiableAt_kk j
      (sin_ne_zero_of_line hcZ y)).continuousAt (continuous_line c).continuousAt
  have hintRK : ∀ i j : ℕ, Integrable (fun y : ℝ =>
      RCd m i ((c : ℂ) + y * I) * kk j ((c : ℂ) + y * I)) := by
    intro i j
    obtain ⟨C, hC⟩ := hdecay i
    refine integrable_of_bound_inv_one_add_sq (C := C * B) ((hcontR i).mul (hcontK j))
      (fun y => ?_)
    rw [norm_mul]
    have hC0 : 0 ≤ C * (1 + y ^ 2)⁻¹ := (norm_nonneg _).trans (hC y)
    calc ‖RCd m i (c + y * I)‖ * ‖kk j (c + y * I)‖ ≤ C * (1 + y ^ 2)⁻¹ * B :=
          mul_le_mul (hC y) (hkB j y) (norm_nonneg _) hC0
      _ = C * B * (1 + y ^ 2)⁻¹ := by ring
  have hlim : ∀ (F : Filter ℝ), Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) F (𝓝 0) →
      ∀ j : ℕ, Tendsto (fun y : ℝ => RCd m j ((c : ℂ) + y * I)) F (𝓝 0) := by
    intro F hF j
    obtain ⟨C, hC⟩ := hdecay j
    refine squeeze_zero_norm hC ?_
    simpa using hF.const_mul C
  have hinvT : Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _
      (tendsto_pow_atTop (by norm_num)))
  have hinvB : Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) atBot (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_neg_atBot_atTop |>.congr
        (fun y => by simp [Function.comp])))
  have hbp := integral_line_by_parts4 (RCd m) kk c
    (fun j _ y => hasDerivAt_RCd m j (hline y))
    (fun j hj y => hasDerivAt_kk hj (sin_ne_zero_of_line hcZ y))
    (hintRK 4 0) (hintRK 0 4) (fun j _ => hlim atTop hinvT j) (fun j _ => hlim atBot hinvB j)
    B (fun j _ y => hkB j y)
  have hFcot : (fun y : ℝ => Fcot (RCd m 4) ((c : ℂ) + y * I))
      = fun y : ℝ => RCd m 4 ((c : ℂ) + y * I) * kk 0 ((c : ℂ) + y * I) := rfl
  have hG0 : (fun y : ℝ => RCd m 0 ((c : ℂ) + y * I) * kk 4 ((c : ℂ) + y * I))
      = fun y : ℝ => Gfn m ((c : ℂ) + y * I) := by
    funext y; rfl
  rw [hFcot, hbp, hG0] at hsum
  -- step 3: conjugation symmetry
  have hint : Integrable (fun y : ℝ => Gfn m ((c : ℂ) + y * I)) := by
    rw [← hG0]; exact hintRK 0 4
  have hsym : ∀ y : ℝ, Gfn m (c + (-y : ℝ) * I) = (starRingEnd ℂ) (Gfn m (c + y * I)) := by
    intro y
    have e : (c : ℂ) + (-y : ℝ) * I = (starRingEnd ℂ) ((c : ℂ) + y * I) := by
      apply Complex.ext <;> simp
    unfold Gfn
    rw [e, map_mul, RC_conj, kk_conj]
  rw [integral_eq_two_re_Ioi hint hsym] at hsum
  have hre := Complex.hasSum_re hsum
  have hterm : (fun t : ℕ => (RCd m 4 ((t : ℂ) + 1)).re)
      = fun t : ℕ => iteratedDeriv 4 (Z7.R m) ((t : ℝ) + 1) := by
    funext t
    rw [← RCd_re_eq m 4 (t := (t : ℝ) + 1) (by have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith)]
    push_cast; rfl
  rw [hterm] at hre
  unfold Z7.L
  rw [hre.tsum_eq]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  generalize (∫ y in Ioi (0 : ℝ), Gfn m (c + y * I)) = J
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have h2π : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [show -(1 / (2 * (π : ℂ))) = ((-(1 / (2 * π)) : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp

end ZetaIrr.Z7.Analytic
