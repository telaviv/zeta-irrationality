/-
# The kernel `k(z) = π cot(πz)` and its first four derivatives

With `C(z) = cos(πz)/sin(πz)` and `S(z) = 1/sin(πz)` (`cotP`, `cscP`), `C' = -πS²`, `S' = -πCS`, and

    k₀ = π C,   k₁ = -π² S²,   k₂ = 2π³ C S²,   k₃ = -2π⁴ (S⁴ + 2C²S²),   k₄ = 8π⁵ (C³S² + 2CS⁴)

(`kk j`, `hasDerivAt_kk`: `(kk j)' = kk (j+1)` where `sin(πz) ≠ 0`). Moreover
* `sin_pow_five_mul_kk4`: `sin⁵(πz) k₄(z) = π⁵ T(z)` with the entire function
  `T(z) = 8 cos(πz) (cos²(πz) + 2)` (`= 2 cos 3πz + 22 cos πz`);
* `T_eq_exp`: `T(z) = e^{-3πiz} (1 + 11q + 11q² + q³)`, `q = e^{2πiz}`;
* `norm_kk_le`: `‖C‖, ‖S‖ ≤ B`, `1 ≤ B` give `‖k_j‖ ≤ 24 π⁵ B⁵`;
* bounds for `C`, `S` on vertical lines `Re z = x` (`sin(πx) ≠ 0`), on `Re z = N + 1/2`, and for
  `|Im z| ≥ y₀ > 0`;
* `tendsto_sub_mul_kk0`: `(z - t) k₀(z) → 1` at every `t ∈ ℕ` (residue 1);
* conjugation symmetry `kk_conj`.
-/
import ZetaIrrational.Analytic.ContourModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

namespace ZetaIrr.Analytic

open Complex Real Filter Topology

/-- `C(z) = cos(πz)/sin(πz)`. -/
noncomputable def cotP (z : ℂ) : ℂ := Complex.cos (π * z) / Complex.sin (π * z)

/-- `S(z) = 1/sin(πz)`. -/
noncomputable def cscP (z : ℂ) : ℂ := 1 / Complex.sin (π * z)

/-- The kernel `k(z) = π cot(πz)` (`j = 0`) and its derivatives `k⁽ʲ⁾`, `j ≤ 4`. -/
noncomputable def kk : ℕ → ℂ → ℂ
  | 0, z => π * cotP z
  | 1, z => -(π : ℂ) ^ 2 * cscP z ^ 2
  | 2, z => 2 * (π : ℂ) ^ 3 * cotP z * cscP z ^ 2
  | 3, z => -2 * (π : ℂ) ^ 4 * (cscP z ^ 4 + 2 * cotP z ^ 2 * cscP z ^ 2)
  | _, z => 8 * (π : ℂ) ^ 5 * (cotP z ^ 3 * cscP z ^ 2 + 2 * cotP z * cscP z ^ 4)

/-- The entire function `T(z) = 8 cos(πz)(cos²(πz) + 2)`. -/
noncomputable def Tfun (z : ℂ) : ℂ := 8 * Complex.cos (π * z) * (Complex.cos (π * z) ^ 2 + 2)

lemma hπC' : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

lemma hasDerivAt_sinπ (w : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.sin (π * w)) (π * Complex.cos (π * w)) w := by
  have := ((hasDerivAt_id w).const_mul (π : ℂ)).csin
  simp only [id, mul_one] at this
  convert this using 1; ring

lemma hasDerivAt_cosπ (w : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.cos (π * w)) (-(π * Complex.sin (π * w))) w := by
  have := ((hasDerivAt_id w).const_mul (π : ℂ)).ccos
  simp only [id, mul_one] at this
  convert this using 1; ring

lemma hasDerivAt_cotP {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    HasDerivAt cotP (-(π : ℂ) * cscP z ^ 2) z := by
  have h := (hasDerivAt_cosπ z).div (hasDerivAt_sinπ z) hz
  unfold cotP cscP
  convert h using 1
  have hsc := Complex.sin_sq_add_cos_sq ((π : ℂ) * z)
  field_simp
  linear_combination hsc

lemma hasDerivAt_cscP {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    HasDerivAt cscP (-(π : ℂ) * cotP z * cscP z) z := by
  have h := (hasDerivAt_sinπ z).inv hz
  unfold cotP cscP
  have he : (fun w : ℂ => 1 / Complex.sin (π * w)) = fun w => (Complex.sin (π * w))⁻¹ := by
    funext w; rw [one_div]
  rw [he]
  convert h using 1
  field_simp

/-- `(kk j)' = kk (j + 1)` for `j < 4`, where `sin(πz) ≠ 0`. -/
theorem hasDerivAt_kk {j : ℕ} (hj : j < 4) {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    HasDerivAt (kk j) (kk (j + 1) z) z := by
  have hC := hasDerivAt_cotP hz
  have hS := hasDerivAt_cscP hz
  interval_cases j
  · have h := hC.const_mul (π : ℂ)
    have hf : kk 0 = fun w => (π : ℂ) * cotP w := by funext w; rfl
    rw [hf]; convert h using 1; simp only [kk]; ring
  · have h := (hS.fun_pow 2).const_mul (-(π : ℂ) ^ 2)
    have hf : kk 1 = fun w => -(π : ℂ) ^ 2 * cscP w ^ 2 := by funext w; rfl
    rw [hf]; convert h using 1; norm_num [kk]; ring
  · have h := (hC.fun_mul (hS.fun_pow 2)).const_mul (2 * (π : ℂ) ^ 3)
    have hf : kk 2 = fun w => 2 * (π : ℂ) ^ 3 * (cotP w * cscP w ^ 2) := by
      funext w; simp only [kk]; ring
    rw [hf]; convert h using 1; norm_num [kk]; ring
  · have h := ((hS.fun_pow 4).fun_add (((hC.fun_pow 2).fun_mul (hS.fun_pow 2)).const_mul 2)).const_mul
      (-2 * (π : ℂ) ^ 4)
    have hf : kk 3 = fun w => -2 * (π : ℂ) ^ 4 * (cscP w ^ 4 + 2 * (cotP w ^ 2 * cscP w ^ 2)) := by
      funext w; simp only [kk]; ring
    rw [hf]; convert h using 1; norm_num [kk]; ring

lemma differentiableAt_kk (j : ℕ) {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    DifferentiableAt ℂ (kk j) z := by
  have hC := (hasDerivAt_cotP hz).differentiableAt
  have hS := (hasDerivAt_cscP hz).differentiableAt
  match j with
  | 0 => exact (hasDerivAt_kk (by norm_num) hz).differentiableAt
  | 1 => exact (hasDerivAt_kk (by norm_num) hz).differentiableAt
  | 2 => exact (hasDerivAt_kk (by norm_num) hz).differentiableAt
  | 3 => exact (hasDerivAt_kk (by norm_num) hz).differentiableAt
  | j + 4 =>
    have hf : kk (j + 4) = fun w => 8 * (π : ℂ) ^ 5 * (cotP w ^ 3 * cscP w ^ 2
        + 2 * cotP w * cscP w ^ 4) := by funext w; rfl
    rw [hf]
    exact ((hC.fun_pow 3 |>.fun_mul (hS.fun_pow 2)).fun_add ((hC.const_mul 2).fun_mul (hS.fun_pow 4))).const_mul _

/-- **The trigonometric identity** `sin⁵(πz) k₄(z) = π⁵ T(z)`. -/
theorem sin_pow_five_mul_kk4 {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    Complex.sin (π * z) ^ 5 * kk 4 z = (π : ℂ) ^ 5 * Tfun z := by
  simp only [kk, cotP, cscP, Tfun]
  have hsc := Complex.sin_sq_add_cos_sq ((π : ℂ) * z)
  field_simp

/-- `T(z) = e^{-3πiz}(1 + 11q + 11q² + q³)` with `q = e^{2πiz}`. -/
theorem T_eq_exp (z : ℂ) :
    Tfun z = Complex.exp (-(3 * π * I * z)) *
      (1 + 11 * Complex.exp (2 * π * I * z) + 11 * Complex.exp (2 * π * I * z) ^ 2
        + Complex.exp (2 * π * I * z) ^ 3) := by
  set A := Complex.exp (π * z * I) with hA
  have hA0 : A ≠ 0 := Complex.exp_ne_zero _
  have hinv : Complex.exp (-(π * z) * I) = A⁻¹ := by
    rw [hA, ← Complex.exp_neg]; ring_nf
  have hq : Complex.exp (2 * π * I * z) = A ^ 2 := by
    rw [hA, ← Complex.exp_nat_mul]; ring_nf
  have h3 : Complex.exp (-(3 * π * I * z)) = (A ^ 3)⁻¹ := by
    rw [hA, ← Complex.exp_nat_mul, ← Complex.exp_neg]; ring_nf
  have hc : Complex.cos (π * z) = (A + A⁻¹) / 2 := by
    rw [Complex.cos, hinv]
  unfold Tfun
  rw [hc, hq, h3]
  field_simp
  ring

/-- `‖1 + 11q + 11q² + q³ - 1‖ ≤ 23 ‖q‖` for `‖q‖ ≤ 1`. -/
lemma norm_Qz_sub_one_le {q : ℂ} (hq : ‖q‖ ≤ 1) :
    ‖(1 + 11 * q + 11 * q ^ 2 + q ^ 3) - 1‖ ≤ 23 * ‖q‖ := by
  have e : (1 + 11 * q + 11 * q ^ 2 + q ^ 3) - 1 = q * (11 + 11 * q + q ^ 2) := by ring
  rw [e, norm_mul]
  have : ‖(11 : ℂ) + 11 * q + q ^ 2‖ ≤ 23 := by
    calc ‖(11 : ℂ) + 11 * q + q ^ 2‖ ≤ ‖(11 : ℂ)‖ + ‖11 * q‖ + ‖q ^ 2‖ := norm_add₃_le
      _ ≤ 11 + 11 * 1 + 1 := by
          simp only [norm_mul, norm_pow]
          have h2 : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hq
          norm_num; linarith
      _ = 23 := by norm_num
  nlinarith [norm_nonneg q]

lemma norm_Qz_le {q : ℂ} (hq : ‖q‖ ≤ 1) : ‖1 + 11 * q + 11 * q ^ 2 + q ^ 3‖ ≤ 24 := by
  have h := norm_Qz_sub_one_le hq
  have h1 : ‖1 + 11 * q + 11 * q ^ 2 + q ^ 3‖ ≤ ‖(1 + 11 * q + 11 * q ^ 2 + q ^ 3) - 1‖ + 1 := by
    have := norm_sub_norm_le (1 + 11 * q + 11 * q ^ 2 + q ^ 3) 1
    simp at this ⊢; linarith
  linarith

/-! ### Size of the kernel -/

/-- `‖k_j‖ ≤ 24 π⁵ B⁵` when `‖C‖, ‖S‖ ≤ B` and `B ≥ 1`. -/
theorem norm_kk_le (j : ℕ) {z : ℂ} {B : ℝ} (hB : 1 ≤ B) (hC : ‖cotP z‖ ≤ B) (hS : ‖cscP z‖ ≤ B) :
    ‖kk j z‖ ≤ 24 * π ^ 5 * B ^ 5 := by
  have hπ1 : 1 ≤ π := by linarith [Real.pi_gt_three]
  have hB0 : 0 ≤ B := by linarith
  have hp : ∀ k ≤ 5, π ^ k ≤ π ^ 5 := fun k hk => pow_le_pow_right₀ hπ1 hk
  have hb : ∀ k ≤ 5, B ^ k ≤ B ^ 5 := fun k hk => pow_le_pow_right₀ hB hk
  have hnC : ∀ k : ℕ, ‖cotP z‖ ^ k ≤ B ^ k := fun k => pow_le_pow_left₀ (norm_nonneg _) hC k
  have hnS : ∀ k : ℕ, ‖cscP z‖ ^ k ≤ B ^ k := fun k => pow_le_pow_left₀ (norm_nonneg _) hS k
  have hnπ : ‖(π : ℂ)‖ = π := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hP5 : 0 ≤ π ^ 5 := by positivity
  have hB5 : 0 ≤ B ^ 5 := by positivity
  match j with
  | 0 =>
    simp only [kk, norm_mul, hnπ]
    have := hp 1 (by norm_num); have := hb 1 (by norm_num)
    simp only [pow_one] at *
    nlinarith [norm_nonneg (cotP z)]
  | 1 =>
    simp only [kk, norm_mul, norm_neg, norm_pow, hnπ]
    have := hp 2 (by norm_num); have := hb 2 (by norm_num); have := hnS 2
    nlinarith [pow_nonneg (norm_nonneg (cscP z)) 2, pow_nonneg Real.pi_pos.le 2]
  | 2 =>
    simp only [kk, norm_mul, norm_pow, hnπ]
    have := hp 3 (by norm_num); have := hb 3 (by norm_num)
    have h1 : ‖cotP z‖ * ‖cscP z‖ ^ 2 ≤ B ^ 3 := by
      calc ‖cotP z‖ * ‖cscP z‖ ^ 2 ≤ B * B ^ 2 := by
            gcongr
        _ = B ^ 3 := by ring
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2]
    have : 2 * π ^ 3 * ‖cotP z‖ * ‖cscP z‖ ^ 2 ≤ 2 * π ^ 5 * B ^ 5 := by
      calc 2 * π ^ 3 * ‖cotP z‖ * ‖cscP z‖ ^ 2 = 2 * π ^ 3 * (‖cotP z‖ * ‖cscP z‖ ^ 2) := by ring
        _ ≤ 2 * π ^ 5 * B ^ 5 := by gcongr; exact h1.trans (hb 3 (by norm_num))
    nlinarith
  | 3 =>
    have h1 : ‖cscP z ^ 4 + 2 * cotP z ^ 2 * cscP z ^ 2‖ ≤ 3 * B ^ 5 := by
      calc ‖cscP z ^ 4 + 2 * cotP z ^ 2 * cscP z ^ 2‖
          ≤ ‖cscP z‖ ^ 4 + 2 * (‖cotP z‖ ^ 2 * ‖cscP z‖ ^ 2) := by
            refine (norm_add_le _ _).trans ?_
            simp [norm_pow, mul_assoc]
        _ ≤ B ^ 4 + 2 * (B ^ 2 * B ^ 2) := by
            gcongr
        _ = 3 * B ^ 4 := by ring
        _ ≤ 3 * B ^ 5 := by have := hb 4 (by norm_num); linarith
    simp only [kk]
    rw [norm_mul, norm_mul, norm_neg, norm_pow, hnπ, show ‖(2 : ℂ)‖ = 2 by simp]
    have := hp 4 (by norm_num)
    calc 2 * π ^ 4 * ‖cscP z ^ 4 + 2 * cotP z ^ 2 * cscP z ^ 2‖ ≤ 2 * π ^ 5 * (3 * B ^ 5) := by
          gcongr
      _ ≤ 24 * π ^ 5 * B ^ 5 := by nlinarith
  | j + 4 =>
    have h1 : ‖cotP z ^ 3 * cscP z ^ 2 + 2 * cotP z * cscP z ^ 4‖ ≤ 3 * B ^ 5 := by
      calc ‖cotP z ^ 3 * cscP z ^ 2 + 2 * cotP z * cscP z ^ 4‖
          ≤ ‖cotP z‖ ^ 3 * ‖cscP z‖ ^ 2 + 2 * (‖cotP z‖ * ‖cscP z‖ ^ 4) := by
            refine (norm_add_le _ _).trans ?_
            simp [norm_pow, mul_assoc]
        _ ≤ B ^ 3 * B ^ 2 + 2 * (B * B ^ 4) := by
            gcongr
        _ = 3 * B ^ 5 := by ring
    have hf : kk (j + 4) z = 8 * (π : ℂ) ^ 5 * (cotP z ^ 3 * cscP z ^ 2
        + 2 * cotP z * cscP z ^ 4) := rfl
    rw [hf, norm_mul, norm_mul, norm_pow, hnπ, show ‖(8 : ℂ)‖ = 8 by simp]
    calc 8 * π ^ 5 * ‖cotP z ^ 3 * cscP z ^ 2 + 2 * cotP z * cscP z ^ 4‖
        ≤ 8 * π ^ 5 * (3 * B ^ 5) := by gcongr
      _ = 24 * π ^ 5 * B ^ 5 := by ring

/-- `‖cos z‖² = cos²(Re z) + sinh²(Im z)`. -/
lemma norm_cos_sq (z : ℂ) :
    ‖Complex.cos z‖ ^ 2 = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have e : Complex.cos z = ((Real.cos z.re * Real.cosh z.im : ℝ) : ℂ)
      - ((Real.sin z.re * Real.sinh z.im : ℝ) : ℂ) * I := by
    rw [Complex.cos_eq]; push_cast; ring
  rw [Complex.sq_norm, Complex.normSq_apply, e]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h1 := Real.cosh_sq z.im
  have h2 := Real.sin_sq_add_cos_sq z.re
  linear_combination (Real.cos z.re ^ 2) * h1 + (Real.sinh z.im ^ 2) * h2

/-- `‖cos z‖² ≤ ‖sin z‖² + 1`. -/
lemma norm_cos_sq_le (z : ℂ) : ‖Complex.cos z‖ ^ 2 ≤ ‖Complex.sin z‖ ^ 2 + 1 := by
  rw [norm_cos_sq, norm_sin_sq]
  nlinarith [Real.sin_sq_add_cos_sq z.re, sq_nonneg (Real.sin z.re)]

/-- `‖C(z)‖² ≤ 1 + ‖S(z)‖²`. -/
lemma norm_cotP_sq_le {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    ‖cotP z‖ ^ 2 ≤ 1 + ‖cscP z‖ ^ 2 := by
  have hpos : 0 < ‖Complex.sin (π * z)‖ := norm_pos_iff.2 hz
  unfold cotP cscP
  rw [norm_div, norm_div, norm_one, div_pow, div_pow, one_pow,
    div_le_iff₀ (by positivity)]
  have := norm_cos_sq_le ((π : ℂ) * z)
  rw [add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  linarith

/-- On the line `Re z = x` with `sin(πx) ≠ 0`: `‖C‖, ‖S‖ ≤ 1/|sin(πx)|`. -/
lemma norm_cotP_cscP_le_of_re {z : ℂ} (hs : Real.sin (π * z.re) ≠ 0) :
    ‖cotP z‖ ≤ 1 / |Real.sin (π * z.re)| ∧ ‖cscP z‖ ≤ 1 / |Real.sin (π * z.re)| := by
  have hre : ((π : ℂ) * z).re = π * z.re := by simp
  have him : ((π : ℂ) * z).im = π * z.im := by simp
  have hsabs : 0 < |Real.sin (π * z.re)| := abs_pos.2 hs
  have hlow := abs_sin_re_le_norm_sin ((π : ℂ) * z)
  rw [hre] at hlow
  have hsin : Complex.sin (π * z) ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; linarith
  have hpos : 0 < ‖Complex.sin (π * z)‖ := norm_pos_iff.2 hsin
  constructor
  · unfold cotP
    rw [norm_div, div_le_div_iff₀ hpos hsabs, one_mul]
    -- `‖cos‖ |sin x| ≤ ‖sin‖`
    have h1 := norm_cos_sq ((π : ℂ) * z)
    have h2 := norm_sin_sq ((π : ℂ) * z)
    rw [hre, him] at h1 h2
    have hsq : (‖Complex.cos (π * z)‖ * |Real.sin (π * z.re)|) ^ 2 ≤ ‖Complex.sin (π * z)‖ ^ 2 := by
      rw [mul_pow, h1, h2, sq_abs]
      have := Real.sin_sq_add_cos_sq (π * z.re)
      have hs1 : Real.sin (π * z.re) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.cos (π * z.re))]
      nlinarith [sq_nonneg (Real.sinh (π * z.im)), sq_nonneg (Real.sin (π * z.re))]
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hsq
  · unfold cscP
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hsabs hlow

/-- On the line `Re z = N + 1/2`: `‖C‖, ‖S‖ ≤ 1`. -/
lemma norm_cotP_cscP_le_half (N : ℕ) (y : ℝ) :
    ‖cotP ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ 1 ∧
      ‖cscP ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ 1 := by
  have hre : ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I).re = (N : ℝ) + 1 / 2 := by simp
  have hs : |Real.sin (π * ((N : ℝ) + 1 / 2))| = 1 := by
    rw [show π * ((N : ℝ) + 1 / 2) = N * π + π / 2 by ring, Real.sin_add_pi_div_two,
      Real.cos_nat_mul_pi, abs_pow, abs_neg, abs_one, one_pow]
  have hs0 : Real.sin (π * ((N : ℝ) + 1 / 2)) ≠ 0 := by
    intro h; rw [h, abs_zero] at hs; norm_num at hs
  have h := norm_cotP_cscP_le_of_re (z := (((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I) (by rw [hre]; exact hs0)
  rw [hre, hs, div_one] at h
  exact h

/-- For `|Im z| ≥ y₀ > 0`: `‖C‖, ‖S‖ ≤ 1 + 1/(π y₀)`. -/
lemma norm_cotP_cscP_le_of_im {z : ℂ} {y₀ : ℝ} (hy₀ : 0 < y₀) (hz : y₀ ≤ |z.im|) :
    ‖cotP z‖ ≤ 1 + 1 / (π * y₀) ∧ ‖cscP z‖ ≤ 1 + 1 / (π * y₀) := by
  have him : ((π : ℂ) * z).im = π * z.im := by simp
  have hlow := abs_sinh_im_le_norm_sin ((π : ℂ) * z)
  rw [him, Real.abs_sinh] at hlow
  have hpy : π * y₀ ≤ |π * z.im| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]; exact mul_le_mul_of_nonneg_left hz Real.pi_pos.le
  have h2 : |π * z.im| ≤ Real.sinh |π * z.im| := Real.self_le_sinh_iff.2 (abs_nonneg _)
  have hπy : 0 < π * y₀ := mul_pos Real.pi_pos hy₀
  have hsin_ge : π * y₀ ≤ ‖Complex.sin (π * z)‖ := by linarith
  have hsin : Complex.sin (π * z) ≠ 0 := by
    intro h; rw [h, norm_zero] at hsin_ge; linarith
  have hS : ‖cscP z‖ ≤ 1 / (π * y₀) := by
    unfold cscP; rw [norm_div, norm_one]; exact one_div_le_one_div_of_le hπy hsin_ge
  have hu : 0 ≤ 1 / (π * y₀) := by positivity
  refine ⟨?_, by linarith⟩
  have hC2 := norm_cotP_sq_le hsin
  have : ‖cotP z‖ ^ 2 ≤ (1 + 1 / (π * y₀)) ^ 2 := by
    have : ‖cscP z‖ ^ 2 ≤ (1 / (π * y₀)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS 2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this

/-! ### Residue and conjugation -/

/-- `(z - t) · π cot(πz) → 1` as `z → t ∈ ℕ`. -/
lemma tendsto_sub_mul_kk0 (t : ℕ) :
    Tendsto (fun z : ℂ => (z - t) * kk 0 z) (𝓝[≠] (t : ℂ)) (𝓝 1) := by
  have hcast : (π : ℂ) * t = ((t * π : ℝ) : ℂ) := by push_cast; ring
  have hcos : Complex.cos (π * t) = (-1 : ℂ) ^ t := by
    rw [hcast, ← Complex.ofReal_cos, Real.cos_nat_mul_pi]; push_cast; rfl
  have hsin : Complex.sin (π * t) = 0 := by
    rw [hcast, ← Complex.ofReal_sin, Real.sin_nat_mul_pi]; simp
  have hd : HasDerivAt (fun z : ℂ => Complex.sin (π * z)) (Complex.cos (π * t) * π) t := by
    have := ((hasDerivAt_id (t : ℂ)).const_mul (π : ℂ)).csin
    simpa using this
  rw [hcos] at hd
  have hslope := hd.tendsto_slope
  have hne : (-1 : ℂ) ^ t * π ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hπC'
  have hinv := hslope.inv₀ hne
  have hcosc : Tendsto (fun z : ℂ => Complex.cos (π * z)) (𝓝[≠] (t : ℂ))
      (𝓝 ((-1 : ℂ) ^ t)) := by
    rw [← hcos]
    exact ((Complex.continuous_cos.comp (continuous_const.mul continuous_id)).tendsto _).mono_left
      nhdsWithin_le_nhds
  have hlim := (hinv.const_mul (π : ℂ)).mul hcosc
  have hval : (π : ℂ) * ((-1 : ℂ) ^ t * π)⁻¹ * (-1 : ℂ) ^ t = 1 := by
    have h1 : ((-1 : ℂ) ^ t) * (-1 : ℂ) ^ t = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [slope_def_field, hsin, sub_zero]
  have : z - t ≠ 0 := sub_ne_zero.2 hz
  simp only [kk, cotP]
  rw [inv_div]
  ring

lemma cotP_conj (z : ℂ) : cotP ((starRingEnd ℂ) z) = (starRingEnd ℂ) (cotP z) := by
  unfold cotP
  rw [map_div₀, ← Complex.sin_conj, ← Complex.cos_conj, map_mul, Complex.conj_ofReal]

lemma cscP_conj (z : ℂ) : cscP ((starRingEnd ℂ) z) = (starRingEnd ℂ) (cscP z) := by
  unfold cscP
  rw [map_div₀, ← Complex.sin_conj, map_mul, Complex.conj_ofReal, map_one]

lemma kk_conj (j : ℕ) (z : ℂ) : kk j ((starRingEnd ℂ) z) = (starRingEnd ℂ) (kk j z) := by
  match j with
  | 0 => simp [kk, cotP_conj]
  | 1 => simp [kk, cscP_conj]
  | 2 => simp [kk, cotP_conj, cscP_conj, map_ofNat]
  | 3 => simp [kk, cotP_conj, cscP_conj, map_ofNat]
  | j + 4 => simp [kk, cotP_conj, cscP_conj, map_ofNat]

end ZetaIrr.Analytic
