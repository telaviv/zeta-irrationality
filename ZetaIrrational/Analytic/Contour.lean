/-
# The contour formula for alternating sums (PROOF_BETA §6.1, PROOF_BETA100 §6.1)

**Theorem** (`hasSum_alternating_eq_line_integral`). Let `f` be holomorphic on `{Re z > c₀}`, with
`‖f z‖ ≤ C (1 + ‖z‖²)⁻¹` for `Re z ≥ c`, where `c > c₀`, `c > -1`, `c ∉ ℤ`, and `f(t) = 0` for the
integers `0 ≤ t < c`. Then

    Σ_{t ≥ 0} (-1)^t f(t) = -(1/2π) ∫_ℝ f(c + iy) π / sin(π(c + iy)) dy
                          = -(1/2πi) ∫_{c-i∞}^{c+i∞} f(z) π / sin(πz) dz.

**Route chosen (no residue theorem in Mathlib).** For `N > c` put `X = N + 1/2`,
`S_N = {t ∈ ℕ : c < t ≤ N}`, `s₀ = c - 1`, and subtract the principal parts:

    G(z) = f(z) π/sin(πz) - Σ_{t ∈ S_N} (-1)^t f(t) m_{t,s₀}(z),    m_{t,s}(z) = (z-t)⁻¹ - (z-s)⁻¹.

1. `G` has only removable singularities in `c ≤ Re z ≤ X` (`Removable.lean`): `(z - t) G(z) → 0`
   at each `t ∈ S_N`.
2. Cauchy's theorem for the rectangle `[c, X] × [-Y, Y]` (Mathlib,
   `integral_boundary_rect_eq_zero_of_differentiableOn`), then `Y → ∞`: the horizontal sides
   are `O(1/Y)`, so `∫_{Re z = c} G = ∫_{Re z = X} G`.
3. The model integrals are explicit (`ContourModel.lean`): `∫_ℝ m_{t,s₀}(c + iy) dy = -2π`,
   `∫_ℝ m_{t,s₀}(X + iy) dy = 0`. Hence
   `∫_ℝ F(c + iy) dy + 2π Σ_{t ≤ N} (-1)^t f(t) = ∫_ℝ F(X + iy) dy` (`line_identity`).
4. `|sin(π(X + iy))| ≥ 1`, so `|∫_ℝ F(X + iy) dy| ≤ C π² / √(1 + X²) → 0` as `N → ∞`.

The conjugate-symmetric form `-(1/π) Re ∫_0^∞ F(c + iy) dy` is `hasSum_alternating_eq_half_line`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Analytic.ContourModel
import ZetaIrrational.Analytic.Removable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.PSeries

set_option autoImplicit false

namespace ZetaIrr.Analytic

open Complex Real MeasureTheory Set Filter Topology Metric

/-- The kernel `π / sin(π z)`. -/
noncomputable def cscPi (z : ℂ) : ℂ := (π : ℂ) / Complex.sin (π * z)

lemma norm_cscPi_le_of_re (x y : ℝ) (hs : Real.sin (π * x) ≠ 0) :
    ‖cscPi (x + y * I)‖ ≤ π / |Real.sin (π * x)| := by
  unfold cscPi
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h := abs_sin_re_le_norm_sin ((π : ℂ) * (x + y * I))
  have hre : ((π : ℂ) * (x + y * I)).re = π * x := by simp
  rw [hre] at h
  exact div_le_div_of_nonneg_left Real.pi_pos.le (abs_pos.2 hs) h

lemma norm_cscPi_le_of_im (x y : ℝ) (hy : y ≠ 0) :
    ‖cscPi (x + y * I)‖ ≤ 1 / |y| := by
  unfold cscPi
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h := abs_sinh_im_le_norm_sin ((π : ℂ) * (x + y * I))
  have him : ((π : ℂ) * (x + y * I)).im = π * y := by simp
  rw [him, Real.abs_sinh] at h
  have hpy : 0 < |π * y| := abs_pos.2 (mul_ne_zero Real.pi_ne_zero hy)
  have h2 : |π * y| ≤ Real.sinh |π * y| := Real.self_le_sinh_iff.2 (abs_nonneg _)
  have h3 : π * |y| ≤ ‖Complex.sin (π * (x + y * I))‖ := by
    rw [abs_mul, abs_of_pos Real.pi_pos] at h2 hpy h; linarith
  rw [div_le_div_iff₀ (by linarith) (abs_pos.2 hy)]
  linarith

lemma norm_cscPi_half_le (N : ℕ) (y : ℝ) :
    ‖cscPi (((N : ℝ) + 1 / 2 : ℝ) + y * I)‖ ≤ π := by
  unfold cscPi
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact div_le_self Real.pi_pos.le (one_le_norm_sin_pi_half N y)

lemma differentiableAt_cscPi {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    DifferentiableAt ℂ cscPi z := by
  unfold cscPi
  exact (differentiableAt_const _).div
    ((Complex.differentiable_sin _).comp z ((differentiableAt_id).const_mul _)) hz

/-- `sin(π z) ≠ 0` for `Re z > -1` unless `z` is a natural number. -/
lemma sin_pi_ne_zero_of_ne_nat {z : ℂ} (hre : -1 < z.re) (hz : ∀ u : ℕ, z ≠ u) :
    Complex.sin (π * z) ≠ 0 := by
  by_cases him : z.im = 0
  · refine sin_pi_ne_zero_of_re (fun k hk => ?_)
    have hk0 : 0 ≤ k := by
      have : (-1 : ℝ) < k := hk ▸ hre
      exact_mod_cast (show (-1 : ℤ) < k by exact_mod_cast this)
    obtain ⟨u, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    exact hz u (Complex.ext (by simpa using hk) (by simpa using him))
  · exact sin_pi_ne_zero_of_im him

/-! ### The main identity for fixed `N` -/

section Identity

variable {f : ℂ → ℂ} {c₀ c C : ℝ}

/-- `F(z) = f(z) π / sin(π z)`. -/
noncomputable def Fker (f : ℂ → ℂ) (z : ℂ) : ℂ := f z * cscPi z

lemma C_nonneg (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) : 0 ≤ C := by
  have h := (norm_nonneg _).trans (hb (c : ℂ) (by simp))
  exact nonneg_of_mul_nonneg_left h (inv_pos.2 (by positivity))

lemma inv_one_add_norm_sq_le (x y : ℝ) : (1 + ‖(x : ℂ) + y * I‖ ^ 2)⁻¹ ≤ (1 + y ^ 2)⁻¹ := by
  apply inv_anti₀ (by positivity)
  have h := Complex.abs_im_le_norm ((x : ℂ) + y * I)
  have him : ((x : ℂ) + y * I).im = y := by simp
  rw [him] at h
  have : y ^ 2 ≤ ‖(x : ℂ) + y * I‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith

lemma continuous_line (x : ℝ) : Continuous (fun y : ℝ => (x : ℂ) + y * I) := by fun_prop

/-- `F` is integrable on the vertical line `Re z = x` when `x ≥ c`, `x > c₀`, `x ∉ ℤ`. -/
lemma integrable_Fker_line (hf : DifferentiableOn ℂ f {z | c₀ < z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) (x : ℝ) (hx : c ≤ x) (hxc : c₀ < x)
    (hs : Real.sin (π * x) ≠ 0) :
    Integrable (fun y : ℝ => Fker f (x + y * I)) := by
  have hC := C_nonneg hb
  have hopen : IsOpen {z : ℂ | c₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsin : ∀ y : ℝ, Complex.sin (π * ((x : ℂ) + y * I)) ≠ 0 := by
    intro y
    refine sin_pi_ne_zero_of_re (fun k hk => hs ?_)
    have hre : ((x : ℂ) + y * I).re = x := by simp
    rw [hre] at hk
    rw [hk, mul_comm]; exact Real.sin_int_mul_pi k
  have hcont : Continuous (fun y : ℝ => Fker f (x + y * I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hz : c₀ < ((x : ℂ) + y * I).re := by simpa using hxc
    have hfa : ContinuousAt f ((x : ℂ) + y * I) :=
      (hf.differentiableAt (hopen.mem_nhds hz)).continuousAt
    have hca : ContinuousAt cscPi ((x : ℂ) + y * I) :=
      (differentiableAt_cscPi (hsin y)).continuousAt
    exact ContinuousAt.comp (g := fun z => f z * cscPi z) (hfa.mul hca)
      (continuous_line x).continuousAt
  refine integrable_of_bound_inv_one_add_sq (C := C * (π / |Real.sin (π * x)|)) hcont
    (fun y => ?_)
  unfold Fker
  rw [norm_mul]
  have h1 := hb ((x : ℂ) + y * I) (by simpa using hx)
  have h2 := norm_cscPi_le_of_re x y hs
  have h3 := inv_one_add_norm_sq_le x y
  calc ‖f (x + y * I)‖ * ‖cscPi (x + y * I)‖
      ≤ (C * (1 + y ^ 2)⁻¹) * (π / |Real.sin (π * x)|) :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h3 hC)) h2 (norm_nonneg _)
          (by positivity)
    _ = C * (π / |Real.sin (π * x)|) * (1 + y ^ 2)⁻¹ := by ring

/-- The bound on the line `Re z = N + 1/2`: `‖∫ F‖ ≤ C π² / √(1 + X²)`. -/
lemma norm_integral_Fker_half_le
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) (N : ℕ) (hN : c ≤ (N : ℝ) + 1 / 2) :
    ‖∫ y : ℝ, Fker f ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I)‖
      ≤ C * π * (π / √(1 + ((N : ℝ) + 1 / 2) ^ 2)) := by
  have hC := C_nonneg hb
  set X : ℝ := (N : ℝ) + 1 / 2 with hX
  set a : ℝ := √(1 + X ^ 2) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = 1 + X ^ 2 := Real.sq_sqrt (by positivity)
  have hint := integrable_inv_sq_add_sq a ha0.ne'
  have hbound : ∀ y : ℝ, ‖Fker f ((X : ℂ) + y * I)‖ ≤ C * π * (a ^ 2 + y ^ 2)⁻¹ := by
    intro y
    unfold Fker
    rw [norm_mul]
    have h1 := hb ((X : ℂ) + y * I) (by simpa using hN)
    have hn : ‖(X : ℂ) + y * I‖ ^ 2 = X ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    rw [hn] at h1
    have h2 := norm_cscPi_half_le N y
    calc ‖f (X + y * I)‖ * ‖cscPi (X + y * I)‖ ≤ C * (1 + (X ^ 2 + y ^ 2))⁻¹ * π :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C * π * (a ^ 2 + y ^ 2)⁻¹ := by rw [ha2]; ring_nf
  calc ‖∫ y : ℝ, Fker f ((X : ℂ) + y * I)‖ ≤ ∫ y : ℝ, C * π * (a ^ 2 + y ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hbound)
    _ = C * π * (π / a) := by rw [integral_const_mul, integral_inv_sq_add_sq a ha0]

/-- The finite set of poles `S_N = {t ∈ ℕ : c < t ≤ N}`. -/
noncomputable def poleSet (c : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter (fun t => c < (t : ℝ))

/-- The subtracted function `G`. -/
noncomputable def Gsub (f : ℂ → ℂ) (c : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  Fker f z - ∑ t ∈ poleSet c N, ((-1 : ℂ) ^ t * f t) * model t (c - 1) z

lemma differentiableAt_model {t s : ℝ} {z : ℂ} (ht : z ≠ t) (hs : z ≠ s) :
    DifferentiableAt ℂ (model t s) z := by
  unfold model
  exact ((differentiableAt_id.sub_const (t : ℂ)).inv (sub_ne_zero.2 ht)).sub
    ((differentiableAt_id.sub_const (s : ℂ)).inv (sub_ne_zero.2 hs))

lemma continuousAt_model {t s : ℝ} {z : ℂ} (ht : z ≠ t) (hs : z ≠ s) :
    ContinuousAt (model t s) z := (differentiableAt_model ht hs).continuousAt

/-- `G` is differentiable at every non-natural point with `Re z ≥ c`. -/
lemma differentiableAt_Gsub (hf : DifferentiableOn ℂ f {z | c₀ < z.re}) (hc₀ : c₀ < c)
    (hc1 : -1 < c) (N : ℕ) {z : ℂ} (hz : c ≤ z.re) (hzn : ∀ u : ℕ, z ≠ u) :
    DifferentiableAt ℂ (Gsub f c N) z := by
  have hopen : IsOpen {z : ℂ | c₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hfz : DifferentiableAt ℂ f z := hf.differentiableAt (hopen.mem_nhds (by
    change c₀ < z.re; linarith))
  have hcsc : DifferentiableAt ℂ cscPi z :=
    differentiableAt_cscPi (sin_pi_ne_zero_of_ne_nat (by linarith) hzn)
  have hs0 : z ≠ ((c - 1 : ℝ) : ℂ) := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold Gsub Fker
  refine (hfz.mul hcsc).sub ?_
  refine DifferentiableAt.fun_sum (fun t _ => ?_)
  exact (differentiableAt_model (by exact_mod_cast hzn t) hs0).const_mul _

/-- The residue condition at each pole. -/
lemma tendsto_Gsub_at_pole (hf : DifferentiableOn ℂ f {z | c₀ < z.re}) (hc₀ : c₀ < c)
    (N : ℕ) {t : ℕ} (ht : t ∈ poleSet c N) :
    Tendsto (fun z => (z - t) * Gsub f c N z) (𝓝[≠] (t : ℂ)) (𝓝 0) := by
  have hct : c < (t : ℝ) := (Finset.mem_filter.1 ht).2
  have hopen : IsOpen {z : ℂ | c₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hft : ContinuousAt f (t : ℂ) := (hf.differentiableAt (hopen.mem_nhds (by
    change c₀ < (t : ℂ).re; simp; linarith))).continuousAt
  have hsub : Tendsto (fun z : ℂ => z - t) (𝓝[≠] (t : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => z - t) (𝓝 (t : ℂ)) (𝓝 ((t : ℂ) - t)) :=
      ((continuous_id (X := ℂ)).sub (continuous_const (y := (t : ℂ)))).tendsto _
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- the `F` part
  have hF : Tendsto (fun z => (z - t) * Fker f z) (𝓝[≠] (t : ℂ)) (𝓝 (f t * (-1 : ℂ) ^ t)) := by
    have h1 := (hft.tendsto.mono_left nhdsWithin_le_nhds).mul (tendsto_sub_mul_pi_div_sin t)
    refine h1.congr (fun z => ?_)
    unfold Fker cscPi; ring
  have hs0 : (t : ℂ) ≠ ((c - 1 : ℝ) : ℂ) := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  -- the model parts
  have hM : ∀ u ∈ poleSet c N, Tendsto (fun z => (z - t) * (((-1 : ℂ) ^ u * f u) *
      model u (c - 1) z)) (𝓝[≠] (t : ℂ)) (𝓝 (if u = t then (-1 : ℂ) ^ u * f u else 0)) := by
    intro u _
    by_cases hut : u = t
    · subst hut
      simp only [↓reduceIte]
      have h1 : Tendsto (fun z : ℂ => (z - u) * ((z : ℂ) - ((c - 1 : ℝ) : ℂ))⁻¹)
          (𝓝[≠] (u : ℂ)) (𝓝 (0 * (((u : ℂ)) - ((c - 1 : ℝ) : ℂ))⁻¹)) := by
        refine hsub.mul ?_
        exact ((((continuous_id (X := ℂ)).sub continuous_const).continuousAt).inv₀
          (sub_ne_zero.2 hs0)).tendsto.mono_left nhdsWithin_le_nhds
      rw [zero_mul] at h1
      have h2 : Tendsto (fun z : ℂ => ((-1 : ℂ) ^ u * f u) * (1 - (z - u) * ((z : ℂ)
          - ((c - 1 : ℝ) : ℂ))⁻¹)) (𝓝[≠] (u : ℂ)) (𝓝 (((-1 : ℂ) ^ u * f u) * (1 - 0))) :=
        (tendsto_const_nhds.sub h1).const_mul _
      rw [sub_zero, mul_one] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z - u ≠ 0 := sub_ne_zero.2 hz
      unfold model
      have : ((u : ℝ) : ℂ) = (u : ℂ) := by push_cast; rfl
      rw [this]
      field_simp
    · simp only [hut, ↓reduceIte]
      have hut' : (t : ℂ) ≠ ((u : ℝ) : ℂ) := by
        intro h; exact hut (by exact_mod_cast h.symm)
      have hc := (continuousAt_model hut' hs0).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {(t : ℂ)}ᶜ))
      have := hsub.mul (hc.const_mul ((-1 : ℂ) ^ u * f u))
      rw [zero_mul] at this
      exact this
  have hsum := tendsto_finsetSum (poleSet c N) hM
  simp only [Finset.sum_ite_eq' (poleSet c N) t, ht, ↓reduceIte] at hsum
  have htot := hF.sub hsum
  rw [show f t * (-1 : ℂ) ^ t - (-1 : ℂ) ^ t * f t = 0 by ring] at htot
  refine htot.congr (fun z => ?_)
  unfold Gsub
  rw [mul_sub, Finset.mul_sum]

/-- `N + 1/2` is not an integer. -/
lemma half_ne_int (N : ℕ) (k : ℤ) : ((N : ℝ) + 1 / 2 : ℝ) ≠ k := by
  intro h
  have h2 : (2 * (N : ℤ) + 1 : ℝ) = 2 * k := by push_cast; linarith
  have h3 : 2 * (N : ℤ) + 1 = 2 * k := by exact_mod_cast h2
  omega

/-- A bound for `G` on horizontal lines. -/
lemma norm_Gsub_horizontal_le (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹)
    (N : ℕ) (x y : ℝ) (hx : c ≤ x) (hy : y ≠ 0) :
    ‖Gsub f c N (x + y * I)‖ ≤
      (C + 2 * ∑ t ∈ poleSet c N, ‖(-1 : ℂ) ^ t * f t‖) / |y| := by
  have hC := C_nonneg hb
  have hy' : 0 < |y| := abs_pos.2 hy
  have hF : ‖Fker f ((x : ℂ) + y * I)‖ ≤ C / |y| := by
    unfold Fker
    rw [norm_mul]
    have h1 := hb ((x : ℂ) + y * I) (by simpa using hx)
    have h1' : ‖f (x + y * I)‖ ≤ C :=
      h1.trans (mul_le_of_le_one_right hC (inv_le_one_of_one_le₀ (by
        have := sq_nonneg ‖(x : ℂ) + y * I‖; linarith)))
    have h2 := norm_cscPi_le_of_im x y hy
    calc ‖f (x + y * I)‖ * ‖cscPi (x + y * I)‖ ≤ C * (1 / |y|) :=
          mul_le_mul h1' h2 (norm_nonneg _) hC
      _ = C / |y| := by ring
  have hinv : ∀ r : ℝ, ‖((x : ℂ) + y * I - r)⁻¹‖ ≤ 1 / |y| := by
    intro r
    rw [norm_inv, one_div]
    apply inv_anti₀ hy'
    have h := Complex.abs_im_le_norm ((x : ℂ) + y * I - r)
    have him : ((x : ℂ) + y * I - r).im = y := by simp
    rwa [him] at h
  have hm : ∀ t : ℕ, ‖model t (c - 1) ((x : ℂ) + y * I)‖ ≤ 2 / |y| := by
    intro t
    unfold model
    calc ‖((x : ℂ) + y * I - (t : ℝ))⁻¹ - ((x : ℂ) + y * I - (c - 1 : ℝ))⁻¹‖
        ≤ ‖((x : ℂ) + y * I - (t : ℝ))⁻¹‖ + ‖((x : ℂ) + y * I - (c - 1 : ℝ))⁻¹‖ :=
          norm_sub_le _ _
      _ ≤ 1 / |y| + 1 / |y| := add_le_add (hinv _) (hinv _)
      _ = 2 / |y| := by ring
  unfold Gsub
  calc ‖Fker f (x + y * I) - ∑ t ∈ poleSet c N, ((-1 : ℂ) ^ t * f t) * model t (c - 1) (x + y * I)‖
      ≤ ‖Fker f (x + y * I)‖ + ∑ t ∈ poleSet c N,
          ‖((-1 : ℂ) ^ t * f t) * model t (c - 1) (x + y * I)‖ :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ C / |y| + ∑ t ∈ poleSet c N, ‖(-1 : ℂ) ^ t * f t‖ * (2 / |y|) := by
        gcongr with t _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hm t) (norm_nonneg _)
    _ = (C + 2 * ∑ t ∈ poleSet c N, ‖(-1 : ℂ) ^ t * f t‖) / |y| := by
        rw [← Finset.sum_mul]; field_simp

/-- **The identity for fixed `N`** (steps 1–3 of the module docstring). -/
theorem line_identity (hf : DifferentiableOn ℂ f {z | c₀ < z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) (hc₀ : c₀ < c) (hc1 : -1 < c)
    (hcZ : ∀ k : ℤ, c ≠ k) (N : ℕ) (hN : c < N) :
    (∫ y : ℝ, Fker f (c + y * I)) + 2 * π * ∑ t ∈ poleSet c N, (-1 : ℂ) ^ t * f t
      = ∫ y : ℝ, Fker f ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I) := by
  classical
  set X : ℝ := (N : ℝ) + 1 / 2 with hX
  have hcX : c < X := by rw [hX]; linarith
  have hXZ : ∀ k : ℤ, X ≠ k := half_ne_int N
  set S := poleSet c N with hS
  set S' : Finset ℂ := S.image (fun t : ℕ => (t : ℂ)) with hS'
  set G := Gsub f c N with hG
  -- points of `S'` are naturals in `(c, X)`
  have hmemS' : ∀ z : ℂ, z ∈ S' → ∃ u : ℕ, u ∈ S ∧ z = u := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hz
    exact ⟨u, hu, rfl⟩
  have hnot : ∀ z : ℂ, (z.re = c ∨ z.re = X ∨ z.im ≠ 0) → z ∉ S' := by
    intro z hz hzS
    obtain ⟨u, _, rfl⟩ := hmemS' z hzS
    simp only [Complex.natCast_re, Complex.natCast_im, ne_eq, not_true_eq_false,
      or_false] at hz
    rcases hz with h | h
    · exact hcZ u (by rw [← h]; norm_cast)
    · exact hXZ u (by rw [← h]; norm_cast)
  -- step 1: removable singularities
  obtain ⟨G', hG'eq, hG'S, hG'd⟩ := exists_removable (G := G) S' (by
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ht'
    have hct : c < (t : ℝ) := (Finset.mem_filter.1 ht).2
    refine ⟨min (1 / 2) ((t : ℝ) - c), lt_min (by norm_num) (by linarith), ?_,
      tendsto_Gsub_at_pole hf hc₀ N ht⟩
    intro z hz hzt
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hz1 : ‖z - t‖ < 1 / 2 := lt_of_lt_of_le hz (min_le_left _ _)
    have hz2 : ‖z - t‖ < (t : ℝ) - c := lt_of_lt_of_le hz (min_le_right _ _)
    have hnat : ∀ u : ℕ, z ≠ u := by
      intro u hu
      subst hu
      have : |(u : ℝ) - t| < 1 / 2 := by
        have h := hz1
        rw [show ((u : ℂ) - (t : ℂ)) = (((u : ℝ) - t : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs] at h
        exact h
      have hut : u = t := by
        rw [abs_lt] at this
        have h1 : (u : ℝ) < t + 1 := by linarith
        have h2 : (t : ℝ) < u + 1 := by linarith
        have h1' : u < t + 1 := by exact_mod_cast h1
        have h2' : t < u + 1 := by exact_mod_cast h2
        omega
      exact hzt (by rw [hut])
    refine ⟨fun hzS => ?_, ?_⟩
    · obtain ⟨u, _, rfl⟩ := hmemS' z hzS
      exact hnat u rfl
    · have hre : c ≤ z.re := by
        have h := Complex.abs_re_le_norm (z - t)
        have : (z - t).re = z.re - t := by simp
        rw [this] at h
        have := (abs_le.1 (h.trans hz2.le)).1
        linarith
      exact differentiableAt_Gsub hf hc₀ hc1 N hre hnat)
  -- step 2: the rectangle, for every `Y > 0`
  have hrect : ∀ Y : ℝ, 0 < Y →
      (∫ x in c..X, G (x + (-Y : ℝ) * I)) - (∫ x in c..X, G (x + Y * I))
        + I • (∫ y in (-Y)..Y, G (X + y * I)) - I • (∫ y in (-Y)..Y, G (c + y * I)) = 0 := by
    intro Y hY
    have H : DifferentiableOn ℂ G' (Set.uIcc ((c : ℂ) - Y * I).re ((X : ℂ) + Y * I).re ×ℂ
        Set.uIcc ((c : ℂ) - Y * I).im ((X : ℂ) + Y * I).im) := by
      intro p hp
      have hpre : p.re ∈ Set.uIcc ((c : ℂ) - Y * I).re ((X : ℂ) + Y * I).re := hp.1
      have e1 : ((c : ℂ) - Y * I).re = c := by simp
      have e3 : ((X : ℂ) + Y * I).re = X := by simp
      rw [e1, e3, Set.uIcc_of_le hcX.le] at hpre
      refine DifferentiableAt.differentiableWithinAt ?_
      by_cases hpS : p ∈ S'
      · exact hG'S p hpS
      · refine hG'd p hpS (differentiableAt_Gsub hf hc₀ hc1 N hpre.1 ?_)
        intro u hu
        apply hpS
        subst hu
        refine Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ?_⟩, rfl⟩
        · have h2 : (u : ℝ) ≤ X := by simpa using hpre.2
          have h3 : (u : ℝ) < N + 1 := by rw [hX] at h2; linarith
          exact_mod_cast h3
        · have h1 : c ≤ (u : ℝ) := by simpa using hpre.1
          exact lt_of_le_of_ne h1 (fun h => hcZ u (by rw [h]; norm_cast))
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G'
      ((c : ℂ) - Y * I) ((X : ℂ) + Y * I) H
    have e1 : ((c : ℂ) - Y * I).re = c := by simp
    have e2 : ((c : ℂ) - Y * I).im = -Y := by simp
    have e3 : ((X : ℂ) + Y * I).re = X := by simp
    have e4 : ((X : ℂ) + Y * I).im = Y := by simp
    rw [e1, e2, e3, e4] at h
    have r1 : (fun x : ℝ => G' (x + (-Y : ℝ) * I)) = fun x : ℝ => G (x + (-Y : ℝ) * I) := by
      funext x; exact hG'eq _ (hnot _ (Or.inr (Or.inr (by simp; exact hY.ne'))))
    have r2 : (fun x : ℝ => G' (x + (Y : ℝ) * I)) = fun x : ℝ => G (x + (Y : ℝ) * I) := by
      funext x; exact hG'eq _ (hnot _ (Or.inr (Or.inr (by simp; exact hY.ne'))))
    have r3 : (fun y : ℝ => G' (X + y * I)) = fun y : ℝ => G (X + y * I) := by
      funext y; exact hG'eq _ (hnot _ (Or.inr (Or.inl (by simp))))
    have r4 : (fun y : ℝ => G' (c + y * I)) = fun y : ℝ => G (c + y * I) := by
      funext y; exact hG'eq _ (hnot _ (Or.inl (by simp)))
    simp only [r1, r2, r3, r4] at h
    exact h
  -- integrability on the two vertical lines
  have hsc : Real.sin (π * c) ≠ 0 := by
    intro h0
    rw [Real.sin_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    exact hcZ k (mul_right_cancel₀ Real.pi_ne_zero (by rw [hk]; ring : (k : ℝ) * π = c * π)).symm
  have hsX : Real.sin (π * X) ≠ 0 := by
    intro h0
    rw [Real.sin_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    exact hXZ k (mul_right_cancel₀ Real.pi_ne_zero (by rw [hk]; ring : (k : ℝ) * π = X * π)).symm
  have hct : ∀ t ∈ S, c ≠ (t : ℝ) := fun t _ h => hcZ t (by rw [h]; norm_cast)
  have htX : ∀ t ∈ S, (t : ℝ) < X := by
    intro t ht
    have h1 := Finset.mem_range.1 (Finset.mem_filter.1 ht).1
    have h' : t ≤ N := by omega
    have : (t : ℝ) ≤ N := by exact_mod_cast h'
    rw [hX]; linarith
  have hFc := integrable_Fker_line hf hb c le_rfl hc₀ hsc
  have hFX := integrable_Fker_line hf hb X hcX.le (by linarith) hsX
  have hMc : ∀ t ∈ S, Integrable (fun y : ℝ => ((-1 : ℂ) ^ t * f t) *
      model t (c - 1) ((c : ℂ) + y * I)) := fun t ht =>
    (integrable_model_line c t (c - 1) (hct t ht) (by linarith)).const_mul _
  have hMX : ∀ t ∈ S, Integrable (fun y : ℝ => ((-1 : ℂ) ^ t * f t) *
      model t (c - 1) ((X : ℂ) + y * I)) := fun t ht =>
    (integrable_model_line X t (c - 1) (htX t ht).ne' (by linarith)).const_mul _
  have hGc : Integrable (fun y : ℝ => G (c + y * I)) :=
    hFc.sub (integrable_finsetSum S hMc)
  have hGX : Integrable (fun y : ℝ => G (X + y * I)) :=
    hFX.sub (integrable_finsetSum S hMX)
  -- step 2': let `Y → ∞`
  set B := C + 2 * ∑ t ∈ S, ‖(-1 : ℂ) ^ t * f t‖ with hB
  have hhor : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      Tendsto (fun Y : ℝ => ∫ x in c..X, G (x + (s * Y : ℝ) * I)) atTop (𝓝 0) := by
    intro s hs
    have hs1 : |s| = 1 := by rcases hs with h | h <;> simp [h]
    have hs0 : s ≠ 0 := by rcases hs with h | h <;> simp [h]
    have hbound : ∀ᶠ Y : ℝ in atTop,
        ‖∫ x in c..X, G (x + (s * Y : ℝ) * I)‖ ≤ B * |X - c| / Y := by
      filter_upwards [eventually_gt_atTop 0] with Y hY
      have hsY : s * Y ≠ 0 := mul_ne_zero hs0 hY.ne'
      have habs : |s * Y| = Y := by rw [abs_mul, hs1, one_mul, abs_of_pos hY]
      calc ‖∫ x in c..X, G (x + (s * Y : ℝ) * I)‖ ≤ B / Y * |X - c| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro x hx
            rw [Set.uIoc_of_le hcX.le] at hx
            have := norm_Gsub_horizontal_le hb N x (s * Y) hx.1.le hsY
            rwa [habs] at this
        _ = B * |X - c| / Y := by ring
    refine squeeze_zero_norm' hbound ?_
    exact tendsto_const_nhds.div_atTop tendsto_id
  have hlimX : Tendsto (fun Y : ℝ => ∫ y in (-Y)..Y, G (X + y * I)) atTop
      (𝓝 (∫ y : ℝ, G (X + y * I))) :=
    intervalIntegral_tendsto_integral hGX tendsto_neg_atTop_atBot tendsto_id
  have hlimc : Tendsto (fun Y : ℝ => ∫ y in (-Y)..Y, G (c + y * I)) atTop
      (𝓝 (∫ y : ℝ, G (c + y * I))) :=
    intervalIntegral_tendsto_integral hGc tendsto_neg_atTop_atBot tendsto_id
  have hlim := (((hhor (-1) (Or.inr rfl)).sub (hhor 1 (Or.inl rfl))).add
    (hlimX.const_smul I)).sub (hlimc.const_smul I)
  have hzero : Tendsto (fun Y : ℝ => (∫ x in c..X, G (x + ((-1) * Y : ℝ) * I))
      - (∫ x in c..X, G (x + (1 * Y : ℝ) * I))
      + I • (∫ y in (-Y)..Y, G (X + y * I)) - I • (∫ y in (-Y)..Y, G (c + y * I)))
      atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with Y hY
    have := hrect Y hY
    simp only [neg_one_mul, one_mul] at this ⊢
    exact this.symm
  have huniq := tendsto_nhds_unique hlim hzero
  rw [sub_self, zero_add, ← smul_sub, smul_eq_mul] at huniq
  have heqG : ∫ y : ℝ, G (X + y * I) = ∫ y : ℝ, G (c + y * I) := by
    have := (mul_eq_zero.1 huniq).resolve_left Complex.I_ne_zero
    exact sub_eq_zero.1 this
  -- step 3: evaluate the model integrals
  have hGc_val : ∫ y : ℝ, G (c + y * I)
      = (∫ y : ℝ, Fker f (c + y * I)) + 2 * π * ∑ t ∈ S, (-1 : ℂ) ^ t * f t := by
    simp only [hG, Gsub]
    rw [integral_sub hFc (integrable_finsetSum S hMc), integral_finsetSum S hMc]
    have : ∀ t ∈ S, ∫ y : ℝ, ((-1 : ℂ) ^ t * f t) * model t (c - 1) ((c : ℂ) + y * I)
        = ((-1 : ℂ) ^ t * f t) * (-2 * π) := by
      intro t ht
      rw [integral_const_mul, integral_model_line_of_lt c t (c - 1)
        (lt_of_le_of_ne (Finset.mem_filter.1 ht).2.le (hct t ht)) (by linarith)]
    rw [Finset.sum_congr rfl this, sub_eq_add_neg, ← Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun t _ => by ring)
  have hGX_val : ∫ y : ℝ, G (X + y * I) = ∫ y : ℝ, Fker f (X + y * I) := by
    simp only [hG, Gsub]
    rw [integral_sub hFX (integrable_finsetSum S hMX), integral_finsetSum S hMX]
    have : ∀ t ∈ S, ∫ y : ℝ, ((-1 : ℂ) ^ t * f t) * model t (c - 1) ((X : ℂ) + y * I) = 0 := by
      intro t ht
      rw [integral_const_mul, integral_model_line_of_gt X t (c - 1) (htX t ht) (by linarith),
        mul_zero]
    rw [Finset.sum_congr rfl this, Finset.sum_const_zero, sub_zero]
  rw [← hGc_val, ← heqG, hGX_val]

lemma summable_inv_one_add_sq_nat : Summable (fun t : ℕ => (1 + (t : ℝ) ^ 2)⁻¹) := by
  have hs2 : Summable (fun t : ℕ => (((t : ℝ) + 1) ^ 2)⁻¹) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
    simpa using this
  refine (hs2.mul_left 2).of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
  rw [show (2 : ℝ) * (((t : ℝ) + 1) ^ 2)⁻¹ = ((((t : ℝ) + 1) ^ 2) / 2)⁻¹ by field_simp]
  exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg ((t : ℝ) - 1)])

/-- **Contour formula for alternating sums** (PROOF_BETA §6.1). -/
theorem hasSum_alternating_eq_line_integral (hf : DifferentiableOn ℂ f {z | c₀ < z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) (hc₀ : c₀ < c) (hc1 : -1 < c)
    (hcZ : ∀ k : ℤ, c ≠ k) (hz : ∀ t : ℕ, (t : ℝ) < c → f t = 0) :
    HasSum (fun t : ℕ => (-1 : ℂ) ^ t * f t)
      (-(1 / (2 * π)) * ∫ y : ℝ, Fker f (c + y * I)) := by
  classical
  have hC := C_nonneg hb
  set a : ℕ → ℂ := fun t => (-1 : ℂ) ^ t * f t with ha
  -- summability
  have hsum : Summable a := by
    refine Summable.of_norm_bounded (summable_inv_one_add_sq_nat.mul_left C) (fun t => ?_)
    simp only [ha, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    by_cases htc : c ≤ (t : ℝ)
    · have h := hb (t : ℂ) (by simpa using htc)
      rwa [Complex.norm_natCast] at h
    · rw [hz t (not_le.1 htc), norm_zero]; positivity
  -- partial sums
  have hpart : ∀ N : ℕ, c < N → ∑ t ∈ Finset.range (N + 1), a t = ∑ t ∈ poleSet c N, a t := by
    intro N _
    unfold poleSet
    rw [Finset.sum_filter_of_ne]
    intro t _ hat
    by_contra hct
    apply hat
    have : (t : ℝ) < c := lt_of_le_of_ne (not_lt.1 hct) (fun h => hcZ t (by rw [← h]; norm_cast))
    simp [ha, hz t this]
  set L : ℂ := -(1 / (2 * π)) * ∫ y : ℝ, Fker f (c + y * I) with hL
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hXlim : Tendsto (fun N : ℕ => ∫ y : ℝ, Fker f ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I))
      atTop (𝓝 0) := by
    have hev : ∀ᶠ N : ℕ in atTop, ‖∫ y : ℝ, Fker f ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I)‖
        ≤ C * π * π / ((N : ℝ) + 1 / 2) := by
      filter_upwards [eventually_gt_atTop ⌈c⌉₊] with N hN
      have hcN : c ≤ (N : ℝ) + 1 / 2 := by
        have := Nat.le_ceil c
        have : (⌈c⌉₊ : ℝ) < N := by exact_mod_cast hN
        linarith
      refine (norm_integral_Fker_half_le hb N hcN).trans ?_
      have hX : 0 < (N : ℝ) + 1 / 2 := by positivity
      have hsq : (N : ℝ) + 1 / 2 ≤ √(1 + ((N : ℝ) + 1 / 2) ^ 2) :=
        Real.le_sqrt_of_sq_le (by linarith)
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left Real.pi_pos.le hX hsq)
        (by positivity)
    refine squeeze_zero_norm' hev ?_
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlim : Tendsto (fun N : ℕ => ∑ t ∈ Finset.range (N + 1), a t) atTop (𝓝 L) := by
    have h1 : Tendsto (fun N : ℕ => (1 / (2 * π)) * ((∫ y : ℝ,
        Fker f ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I)) - ∫ y : ℝ, Fker f (c + y * I)))
        atTop (𝓝 ((1 / (2 * π)) * (0 - ∫ y : ℝ, Fker f (c + y * I)))) :=
      (hXlim.sub tendsto_const_nhds).const_mul _
    rw [zero_sub, mul_neg, ← neg_mul] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop ⌈c⌉₊] with N hN
    have hcN : c < N := lt_of_le_of_lt (Nat.le_ceil c) (by exact_mod_cast hN)
    rw [hpart N hcN, ← line_identity hf hb hc₀ hc1 hcZ N hcN, add_sub_cancel_left]
    simp only [ha]
    field_simp
  have h2 := (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have heq := tendsto_nhds_unique h2 hlim
  rw [← heq]
  exact hsum.hasSum

/-- The same formula as a contour integral: `Σ (-1)^t f(t) = -(1/2πi) ∫_{c-i∞}^{c+i∞} F(z) dz`,
with `dz = i dy`. -/
theorem hasSum_alternating_eq_contour (hf : DifferentiableOn ℂ f {z | c₀ < z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) (hc₀ : c₀ < c) (hc1 : -1 < c)
    (hcZ : ∀ k : ℤ, c ≠ k) (hz : ∀ t : ℕ, (t : ℝ) < c → f t = 0) :
    HasSum (fun t : ℕ => (-1 : ℂ) ^ t * f t)
      (-(1 / (2 * π * I)) * (I * ∫ y : ℝ, Fker f (c + y * I))) := by
  convert hasSum_alternating_eq_line_integral hf hb hc₀ hc1 hcZ hz using 1
  field_simp

/-- For `g(-y) = conj g(y)`, `∫_ℝ g = 2 Re ∫_0^∞ g`. -/
lemma integral_eq_two_re_Ioi {g : ℝ → ℂ} (hg : Integrable g)
    (hsym : ∀ y, g (-y) = (starRingEnd ℂ) (g y)) :
    ∫ y, g y = ((2 * (∫ y in Ioi (0 : ℝ), g y).re : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hg.integrableOn hg.integrableOn]
  have h1 : ∫ y in Iic (0 : ℝ), g y = ∫ y in Iic (0 : ℝ), (starRingEnd ℂ) (g (-y)) := by
    congr 1; funext y; rw [hsym, Complex.conj_conj]
  rw [h1, integral_comp_neg_Iic 0 (fun y => (starRingEnd ℂ) (g y)), neg_zero, integral_conj,
    add_comm, Complex.add_conj]

lemma cscPi_conj (z : ℂ) : cscPi ((starRingEnd ℂ) z) = (starRingEnd ℂ) (cscPi z) := by
  unfold cscPi
  rw [map_div₀, Complex.conj_ofReal, ← Complex.sin_conj, map_mul, Complex.conj_ofReal]

/-- **Contour formula, conjugate-symmetric form.** If moreover `f(c - iy) = conj f(c + iy)`
(e.g. `f` real on `ℝ`), then `Σ (-1)^t f(t) = -(1/π) Re ∫_0^∞ F(c + iy) dy`,
i.e. `-(1/π) Im ∫_c^{c+i∞} F(z) dz`. -/
theorem hasSum_alternating_eq_half_line (hf : DifferentiableOn ℂ f {z | c₀ < z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) (hc₀ : c₀ < c) (hc1 : -1 < c)
    (hcZ : ∀ k : ℤ, c ≠ k) (hz : ∀ t : ℕ, (t : ℝ) < c → f t = 0)
    (hconj : ∀ y : ℝ, f (c + (-y : ℝ) * I) = (starRingEnd ℂ) (f (c + y * I))) :
    HasSum (fun t : ℕ => (-1 : ℂ) ^ t * f t)
      ((-(1 / π) * (∫ y in Ioi (0 : ℝ), Fker f (c + y * I)).re : ℝ) : ℂ) := by
  have hsc : Real.sin (π * c) ≠ 0 := by
    intro h0
    rw [Real.sin_eq_zero_iff] at h0
    obtain ⟨k, hk⟩ := h0
    exact hcZ k (mul_right_cancel₀ Real.pi_ne_zero (by rw [hk]; ring : (k : ℝ) * π = c * π)).symm
  have hint := integrable_Fker_line hf hb c le_rfl hc₀ hsc
  have hsym : ∀ y : ℝ, Fker f (c + (-y : ℝ) * I) = (starRingEnd ℂ) (Fker f (c + y * I)) := by
    intro y
    unfold Fker
    have e : (c : ℂ) + (-y : ℝ) * I = (starRingEnd ℂ) ((c : ℂ) + y * I) := by
      apply Complex.ext <;> simp
    rw [map_mul, hconj y, e, cscPi_conj]
  have h := hasSum_alternating_eq_line_integral hf hb hc₀ hc1 hcZ hz
  rw [integral_eq_two_re_Ioi hint hsym] at h
  convert h using 1
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  generalize (∫ y in Ioi (0 : ℝ), Fker f (c + y * I)) = J
  push_cast
  field_simp

end Identity

end ZetaIrr.Analytic
