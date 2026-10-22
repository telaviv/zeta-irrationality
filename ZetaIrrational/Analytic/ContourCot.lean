/-
# The contour formula for `Σ_{t ≥ 1} f(t)` with the kernel `π cot(πz)` (Lemma 6)

**Theorem** (`hasSum_cot_eq_line_integral`). Let `f` be holomorphic on `{Re z > c₀}`, with
`‖f z‖ ≤ C (1 + ‖z‖²)⁻¹` for `Re z ≥ c`, where `0 ≤ c₀ < c`, `c ∉ ℤ`, and `f(t) = 0` for the
integers `1 ≤ t < c`. Then

    Σ_{t ≥ 1} f(t) = -(1/2π) ∫_ℝ f(c + iy) π cot(π(c + iy)) dy
                   = -(1/2πi) ∫_{c-i∞}^{c+i∞} f(z) π cot(πz) dz.

**Route (Mathlib has no residue theorem).** For `N > c` put `X = N + 1/2` and subtract the principal
parts at the integers `c < t ≤ N` (`GsubC`, with the model kernel `m_{t,s}` of `ContourModel.lean`).
The difference has only removable singularities (`Removable.lean`), so Cauchy's theorem for the
rectangle `[c, X] × [-Y, Y]` (`integral_boundary_rect_eq_zero_of_differentiableOn`) and `Y → ∞`
(`norm_GsubC_horizontal_le`) give `line_identity_cot`; then `N → ∞`. The kernel `k₀ = π cot(πz)`
(`CotKernel.lean`) has residue `1` at every integer (`tendsto_sub_mul_kk0`), `‖k₀‖ ≤ π` on
`Re z = N + 1/2`, `‖k₀‖ ≤ π/|sin(πc)|` on `Re z = c`, and `‖k₀‖ ≤ 2π` for `|Im z| ≥ 1`. The pole at
`0` lies outside the strip `c ≤ Re z ≤ N + 1/2`.
-/
import ZetaIrrational.Analytic.ContourCommon
import ZetaIrrational.Analytic.CotKernel

set_option autoImplicit false

namespace ZetaIrr.Analytic

open Complex Real MeasureTheory Set Filter Topology Metric

section IdentityCot

variable {f : ℂ → ℂ} {c₀ c C : ℝ}

/-- `F(z) = f(z) π cot(π z)`. -/
noncomputable def Fcot (f : ℂ → ℂ) (z : ℂ) : ℂ := f z * kk 0 z

lemma norm_kk0_le_of_re (x y : ℝ) (hs : Real.sin (π * x) ≠ 0) :
    ‖kk 0 (x + y * I)‖ ≤ π / |Real.sin (π * x)| := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have h := (norm_cotP_cscP_le_of_re (z := (x : ℂ) + y * I) (by rw [hre]; exact hs)).1
  rw [hre] at h
  simp only [kk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc π * ‖cotP (x + y * I)‖ ≤ π * (1 / |Real.sin (π * x)|) :=
        mul_le_mul_of_nonneg_left h Real.pi_pos.le
    _ = π / |Real.sin (π * x)| := by ring

lemma norm_kk0_le_of_im (x y : ℝ) (hy : 1 ≤ |y|) : ‖kk 0 (x + y * I)‖ ≤ 2 * π := by
  have him : ((x : ℂ) + y * I).im = y := by simp
  have h := (norm_cotP_cscP_le_of_im (z := (x : ℂ) + y * I) (y₀ := 1) one_pos
    (by rw [him]; exact hy)).1
  have hπ : 1 / (π * 1) ≤ 1 := by
    rw [mul_one, div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  simp only [kk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos]

lemma norm_kk0_half_le (N : ℕ) (y : ℝ) :
    ‖kk 0 (((N : ℝ) + 1 / 2 : ℝ) + y * I)‖ ≤ π := by
  have h := (norm_cotP_cscP_le_half N y).1
  simp only [kk, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos]

lemma differentiableAt_kk0 {z : ℂ} (hz : Complex.sin (π * z) ≠ 0) :
    DifferentiableAt ℂ (kk 0) z := differentiableAt_kk 0 hz

/-- `F` is integrable on the vertical line `Re z = x` when `x ≥ c`, `x > c₀`, `x ∉ ℤ`. -/
lemma integrable_Fcot_line (hf : DifferentiableOn ℂ f {z | c₀ < z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) (x : ℝ) (hx : c ≤ x) (hxc : c₀ < x)
    (hs : Real.sin (π * x) ≠ 0) :
    Integrable (fun y : ℝ => Fcot f (x + y * I)) := by
  have hC := C_nonneg hb
  have hopen : IsOpen {z : ℂ | c₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsin : ∀ y : ℝ, Complex.sin (π * ((x : ℂ) + y * I)) ≠ 0 := by
    intro y
    refine sin_pi_ne_zero_of_re (fun k hk => hs ?_)
    have hre : ((x : ℂ) + y * I).re = x := by simp
    rw [hre] at hk
    rw [hk, mul_comm]; exact Real.sin_int_mul_pi k
  have hcont : Continuous (fun y : ℝ => Fcot f (x + y * I)) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hz : c₀ < ((x : ℂ) + y * I).re := by simpa using hxc
    have hfa : ContinuousAt f ((x : ℂ) + y * I) :=
      (hf.differentiableAt (hopen.mem_nhds hz)).continuousAt
    have hca : ContinuousAt (kk 0) ((x : ℂ) + y * I) :=
      (differentiableAt_kk0 (hsin y)).continuousAt
    exact ContinuousAt.comp (g := fun z => f z * kk 0 z) (hfa.mul hca)
      (continuous_line x).continuousAt
  refine integrable_of_bound_inv_one_add_sq (C := C * (π / |Real.sin (π * x)|)) hcont
    (fun y => ?_)
  unfold Fcot
  rw [norm_mul]
  have h1 := hb ((x : ℂ) + y * I) (by simpa using hx)
  have h2 := norm_kk0_le_of_re x y hs
  have h3 := inv_one_add_norm_sq_le x y
  calc ‖f (x + y * I)‖ * ‖kk 0 (x + y * I)‖
      ≤ (C * (1 + y ^ 2)⁻¹) * (π / |Real.sin (π * x)|) :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h3 hC)) h2 (norm_nonneg _)
          (by positivity)
    _ = C * (π / |Real.sin (π * x)|) * (1 + y ^ 2)⁻¹ := by ring

/-- The bound on the line `Re z = N + 1/2`: `‖∫ F‖ ≤ C π² / √(1 + X²)`. -/
lemma norm_integral_Fcot_half_le
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) (N : ℕ) (hN : c ≤ (N : ℝ) + 1 / 2) :
    ‖∫ y : ℝ, Fcot f ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I)‖
      ≤ C * π * (π / √(1 + ((N : ℝ) + 1 / 2) ^ 2)) := by
  have hC := C_nonneg hb
  set X : ℝ := (N : ℝ) + 1 / 2 with hX
  set a : ℝ := √(1 + X ^ 2) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = 1 + X ^ 2 := Real.sq_sqrt (by positivity)
  have hint := integrable_inv_sq_add_sq a ha0.ne'
  have hbound : ∀ y : ℝ, ‖Fcot f ((X : ℂ) + y * I)‖ ≤ C * π * (a ^ 2 + y ^ 2)⁻¹ := by
    intro y
    unfold Fcot
    rw [norm_mul]
    have h1 := hb ((X : ℂ) + y * I) (by simpa using hN)
    have hn : ‖(X : ℂ) + y * I‖ ^ 2 = X ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    rw [hn] at h1
    have h2 := norm_kk0_half_le N y
    calc ‖f (X + y * I)‖ * ‖kk 0 (X + y * I)‖ ≤ C * (1 + (X ^ 2 + y ^ 2))⁻¹ * π :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C * π * (a ^ 2 + y ^ 2)⁻¹ := by rw [ha2]; ring_nf
  calc ‖∫ y : ℝ, Fcot f ((X : ℂ) + y * I)‖ ≤ ∫ y : ℝ, C * π * (a ^ 2 + y ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hbound)
    _ = C * π * (π / a) := by rw [integral_const_mul, integral_inv_sq_add_sq a ha0]

/-- The subtracted function `G`. -/
noncomputable def GsubC (f : ℂ → ℂ) (c : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  Fcot f z - ∑ t ∈ poleSet c N, f t * model t (c - 1) z

/-- `G` is differentiable at every non-natural point with `Re z ≥ c`. -/
lemma differentiableAt_GsubC (hf : DifferentiableOn ℂ f {z | c₀ < z.re}) (hc₀ : c₀ < c)
    (hc1 : -1 < c) (N : ℕ) {z : ℂ} (hz : c ≤ z.re) (hzn : ∀ u : ℕ, z ≠ u) :
    DifferentiableAt ℂ (GsubC f c N) z := by
  have hopen : IsOpen {z : ℂ | c₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hfz : DifferentiableAt ℂ f z := hf.differentiableAt (hopen.mem_nhds (by
    change c₀ < z.re; linarith))
  have hk : DifferentiableAt ℂ (kk 0) z :=
    differentiableAt_kk0 (sin_pi_ne_zero_of_ne_nat (by linarith) hzn)
  have hs0 : z ≠ ((c - 1 : ℝ) : ℂ) := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold GsubC Fcot
  refine (hfz.mul hk).sub ?_
  refine DifferentiableAt.fun_sum (fun t _ => ?_)
  exact (differentiableAt_model (by exact_mod_cast hzn t) hs0).const_mul _

/-- The residue condition at each pole. -/
lemma tendsto_GsubC_at_pole (hf : DifferentiableOn ℂ f {z | c₀ < z.re}) (hc₀ : c₀ < c)
    (N : ℕ) {t : ℕ} (ht : t ∈ poleSet c N) :
    Tendsto (fun z => (z - t) * GsubC f c N z) (𝓝[≠] (t : ℂ)) (𝓝 0) := by
  have hct : c < (t : ℝ) := (Finset.mem_filter.1 ht).2
  have hopen : IsOpen {z : ℂ | c₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hft : ContinuousAt f (t : ℂ) := (hf.differentiableAt (hopen.mem_nhds (by
    change c₀ < (t : ℂ).re; simp; linarith))).continuousAt
  have hsub : Tendsto (fun z : ℂ => z - t) (𝓝[≠] (t : ℂ)) (𝓝 0) := by
    have h : Tendsto (fun z : ℂ => z - t) (𝓝 (t : ℂ)) (𝓝 ((t : ℂ) - t)) :=
      ((continuous_id (X := ℂ)).sub (continuous_const (y := (t : ℂ)))).tendsto _
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hF : Tendsto (fun z => (z - t) * Fcot f z) (𝓝[≠] (t : ℂ)) (𝓝 (f t * 1)) := by
    have h1 := (hft.tendsto.mono_left nhdsWithin_le_nhds).mul (tendsto_sub_mul_kk0 t)
    refine h1.congr (fun z => ?_)
    unfold Fcot; ring
  have hs0 : (t : ℂ) ≠ ((c - 1 : ℝ) : ℂ) := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hM : ∀ u ∈ poleSet c N, Tendsto (fun z => (z - t) * (f u * model u (c - 1) z))
      (𝓝[≠] (t : ℂ)) (𝓝 (if u = t then f u else 0)) := by
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
      have h2 : Tendsto (fun z : ℂ => f u * (1 - (z - u) * ((z : ℂ)
          - ((c - 1 : ℝ) : ℂ))⁻¹)) (𝓝[≠] (u : ℂ)) (𝓝 (f u * (1 - 0))) :=
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
      have := hsub.mul (hc.const_mul (f u))
      rw [zero_mul] at this
      exact this
  have hsum := tendsto_finsetSum (poleSet c N) hM
  simp only [Finset.sum_ite_eq' (poleSet c N) t, ht, ↓reduceIte] at hsum
  have htot := hF.sub hsum
  rw [show f t * 1 - f t = 0 by ring] at htot
  refine htot.congr (fun z => ?_)
  unfold GsubC
  rw [mul_sub, Finset.mul_sum]

/-- A bound for `G` on horizontal lines `|y| ≥ 1`. -/
lemma norm_GsubC_horizontal_le (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹)
    (N : ℕ) (x y : ℝ) (hx : c ≤ x) (hy : 1 ≤ |y|) :
    ‖GsubC f c N (x + y * I)‖ ≤
      (2 * π * C + 2 * ∑ t ∈ poleSet c N, ‖f t‖) / |y| := by
  have hC := C_nonneg hb
  have hy' : 0 < |y| := by linarith
  have hF : ‖Fcot f ((x : ℂ) + y * I)‖ ≤ 2 * π * C / |y| := by
    unfold Fcot
    rw [norm_mul]
    have h1 := hb ((x : ℂ) + y * I) (by simpa using hx)
    have h3 := inv_one_add_norm_sq_le x y
    have h4 : (1 + y ^ 2)⁻¹ ≤ 1 / |y| := by
      rw [one_div]
      apply inv_anti₀ hy'
      have : |y| ≤ y ^ 2 := by rw [← sq_abs]; nlinarith
      linarith
    have h1' : ‖f (x + y * I)‖ ≤ C / |y| := by
      calc ‖f (x + y * I)‖ ≤ C * (1 + y ^ 2)⁻¹ := h1.trans (mul_le_mul_of_nonneg_left h3 hC)
        _ ≤ C * (1 / |y|) := mul_le_mul_of_nonneg_left h4 hC
        _ = C / |y| := by ring
    have h2 := norm_kk0_le_of_im x y hy
    calc ‖f (x + y * I)‖ * ‖kk 0 (x + y * I)‖ ≤ C / |y| * (2 * π) :=
          mul_le_mul h1' h2 (norm_nonneg _) (by positivity)
      _ = 2 * π * C / |y| := by ring
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
  unfold GsubC
  calc ‖Fcot f (x + y * I) - ∑ t ∈ poleSet c N, f t * model t (c - 1) (x + y * I)‖
      ≤ ‖Fcot f (x + y * I)‖ + ∑ t ∈ poleSet c N,
          ‖f t * model t (c - 1) (x + y * I)‖ :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ 2 * π * C / |y| + ∑ t ∈ poleSet c N, ‖f t‖ * (2 / |y|) := by
        gcongr with t _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hm t) (norm_nonneg _)
    _ = (2 * π * C + 2 * ∑ t ∈ poleSet c N, ‖f t‖) / |y| := by
        rw [← Finset.sum_mul]; field_simp

/-- **The identity for fixed `N`.** -/
theorem line_identity_cot (hf : DifferentiableOn ℂ f {z | c₀ < z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) (hc₀ : c₀ < c) (hc1 : -1 < c)
    (hcZ : ∀ k : ℤ, c ≠ k) (N : ℕ) (hN : c < N) :
    (∫ y : ℝ, Fcot f (c + y * I)) + 2 * π * ∑ t ∈ poleSet c N, f t
      = ∫ y : ℝ, Fcot f ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I) := by
  classical
  set X : ℝ := (N : ℝ) + 1 / 2 with hX
  have hcX : c < X := by rw [hX]; linarith
  have hXZ : ∀ k : ℤ, X ≠ k := half_ne_int N
  set S := poleSet c N with hS
  set S' : Finset ℂ := S.image (fun t : ℕ => (t : ℂ)) with hS'
  set G := GsubC f c N with hG
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
  obtain ⟨G', hG'eq, hG'S, hG'd⟩ := exists_removable (G := G) S' (by
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ht'
    have hct : c < (t : ℝ) := (Finset.mem_filter.1 ht).2
    refine ⟨min (1 / 2) ((t : ℝ) - c), lt_min (by norm_num) (by linarith), ?_,
      tendsto_GsubC_at_pole hf hc₀ N ht⟩
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
      exact differentiableAt_GsubC hf hc₀ hc1 N hre hnat)
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
      · refine hG'd p hpS (differentiableAt_GsubC hf hc₀ hc1 N hpre.1 ?_)
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
  have hFc := integrable_Fcot_line hf hb c le_rfl hc₀ hsc
  have hFX := integrable_Fcot_line hf hb X hcX.le (by linarith) hsX
  have hMc : ∀ t ∈ S, Integrable (fun y : ℝ => f t *
      model t (c - 1) ((c : ℂ) + y * I)) := fun t ht =>
    (integrable_model_line c t (c - 1) (hct t ht) (by linarith)).const_mul _
  have hMX : ∀ t ∈ S, Integrable (fun y : ℝ => f t *
      model t (c - 1) ((X : ℂ) + y * I)) := fun t ht =>
    (integrable_model_line X t (c - 1) (htX t ht).ne' (by linarith)).const_mul _
  have hGc : Integrable (fun y : ℝ => G (c + y * I)) :=
    hFc.sub (integrable_finsetSum S hMc)
  have hGX : Integrable (fun y : ℝ => G (X + y * I)) :=
    hFX.sub (integrable_finsetSum S hMX)
  set B := 2 * π * C + 2 * ∑ t ∈ S, ‖f t‖ with hB
  have hhor : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      Tendsto (fun Y : ℝ => ∫ x in c..X, G (x + (s * Y : ℝ) * I)) atTop (𝓝 0) := by
    intro s hs
    have hs1 : |s| = 1 := by rcases hs with h | h <;> simp [h]
    have hbound : ∀ᶠ Y : ℝ in atTop,
        ‖∫ x in c..X, G (x + (s * Y : ℝ) * I)‖ ≤ B * |X - c| / Y := by
      filter_upwards [eventually_ge_atTop 1] with Y hY
      have habs : |s * Y| = Y := by rw [abs_mul, hs1, one_mul, abs_of_pos (by linarith)]
      calc ‖∫ x in c..X, G (x + (s * Y : ℝ) * I)‖ ≤ B / Y * |X - c| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro x hx
            rw [Set.uIoc_of_le hcX.le] at hx
            have := norm_GsubC_horizontal_le hb N x (s * Y) hx.1.le (by rw [habs]; exact hY)
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
  have hGc_val : ∫ y : ℝ, G (c + y * I)
      = (∫ y : ℝ, Fcot f (c + y * I)) + 2 * π * ∑ t ∈ S, f t := by
    simp only [hG, GsubC]
    rw [integral_sub hFc (integrable_finsetSum S hMc), integral_finsetSum S hMc]
    have : ∀ t ∈ S, ∫ y : ℝ, f t * model t (c - 1) ((c : ℂ) + y * I)
        = f t * (-2 * π) := by
      intro t ht
      rw [integral_const_mul, integral_model_line_of_lt c t (c - 1)
        (lt_of_le_of_ne (Finset.mem_filter.1 ht).2.le (hct t ht)) (by linarith)]
    rw [Finset.sum_congr rfl this, sub_eq_add_neg, ← Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun t _ => by ring)
  have hGX_val : ∫ y : ℝ, G (X + y * I) = ∫ y : ℝ, Fcot f (X + y * I) := by
    simp only [hG, GsubC]
    rw [integral_sub hFX (integrable_finsetSum S hMX), integral_finsetSum S hMX]
    have : ∀ t ∈ S, ∫ y : ℝ, f t * model t (c - 1) ((X : ℂ) + y * I) = 0 := by
      intro t ht
      rw [integral_const_mul, integral_model_line_of_gt X t (c - 1) (htX t ht) (by linarith),
        mul_zero]
    rw [Finset.sum_congr rfl this, Finset.sum_const_zero, sub_zero]
  rw [← hGc_val, ← heqG, hGX_val]

/-- **Contour formula for `Σ_{t ≥ 1} f(t)`.** -/
theorem hasSum_cot_eq_line_integral (hf : DifferentiableOn ℂ f {z | c₀ < z.re})
    (hb : ∀ z : ℂ, c ≤ z.re → ‖f z‖ ≤ C * (1 + ‖z‖ ^ 2)⁻¹) (hc₀ : c₀ < c) (hc0 : 0 < c)
    (hcZ : ∀ k : ℤ, c ≠ k) (hz : ∀ t : ℕ, 1 ≤ t → (t : ℝ) < c → f t = 0) :
    HasSum (fun t : ℕ => f ((t : ℂ) + 1))
      (-(1 / (2 * π)) * ∫ y : ℝ, Fcot f (c + y * I)) := by
  classical
  have hC := C_nonneg hb
  set a : ℕ → ℂ := fun t => if t = 0 then 0 else f t with ha
  have ha0 : ∀ t : ℕ, (t : ℝ) < c → a t = 0 := by
    intro t ht
    simp only [ha]
    split_ifs with h
    · rfl
    · exact hz t (Nat.one_le_iff_ne_zero.2 h) ht
  have hsum : Summable a := by
    refine Summable.of_norm_bounded (summable_inv_one_add_sq_nat.mul_left C) (fun t => ?_)
    by_cases htc : c ≤ (t : ℝ)
    · have ht0 : t ≠ 0 := by
        intro h; subst h; simp at htc; linarith
      simp only [ha, ht0, ↓reduceIte]
      have h := hb (t : ℂ) (by simpa using htc)
      rwa [Complex.norm_natCast] at h
    · rw [ha0 t (not_le.1 htc), norm_zero]; positivity
  have hpart : ∀ N : ℕ, c < N → ∑ t ∈ Finset.range (N + 1), a t = ∑ t ∈ poleSet c N, f t := by
    intro N _
    unfold poleSet
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    split_ifs with hct
    · have ht0 : t ≠ 0 := by
        intro h; subst h; simp at hct; linarith
      simp [ha, ht0]
    · exact ha0 t (lt_of_le_of_ne (not_lt.1 hct) (fun h => hcZ t (by rw [← h]; norm_cast)))
  set L : ℂ := -(1 / (2 * π)) * ∫ y : ℝ, Fcot f (c + y * I) with hL
  have hXlim : Tendsto (fun N : ℕ => ∫ y : ℝ, Fcot f ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I))
      atTop (𝓝 0) := by
    have hev : ∀ᶠ N : ℕ in atTop, ‖∫ y : ℝ, Fcot f ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I)‖
        ≤ C * π * π / ((N : ℝ) + 1 / 2) := by
      filter_upwards [eventually_gt_atTop ⌈c⌉₊] with N hN
      have hcN : c ≤ (N : ℝ) + 1 / 2 := by
        have := Nat.le_ceil c
        have : (⌈c⌉₊ : ℝ) < N := by exact_mod_cast hN
        linarith
      refine (norm_integral_Fcot_half_le hb N hcN).trans ?_
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
        Fcot f ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) + y * I)) - ∫ y : ℝ, Fcot f (c + y * I)))
        atTop (𝓝 ((1 / (2 * π)) * (0 - ∫ y : ℝ, Fcot f (c + y * I)))) :=
      (hXlim.sub tendsto_const_nhds).const_mul _
    rw [zero_sub, mul_neg, ← neg_mul] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop ⌈c⌉₊] with N hN
    have hcN : c < N := lt_of_le_of_lt (Nat.le_ceil c) (by exact_mod_cast hN)
    rw [hpart N hcN, ← line_identity_cot hf hb hc₀ (by linarith) hcZ N hcN, add_sub_cancel_left]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  have h2 := (hsum.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have heq := tendsto_nhds_unique h2 hlim
  have hA : HasSum a L := by rw [← heq]; exact hsum.hasSum
  have hshift := (hasSum_nat_add_iff' 1).2 hA
  simp only [Finset.sum_range_one, ha, ↓reduceIte, sub_zero] at hshift
  refine hshift.congr_fun (fun t => ?_)
  simp

end IdentityCot

end ZetaIrr.Analytic
