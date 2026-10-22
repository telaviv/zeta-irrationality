/-
# Contour deformation via primitives (Lemma 6)

Mathlib has primitives of holomorphic functions on discs (`DifferentiableOn.isExactOn_ball`).
We extend this to
* nested unions of discs (`exists_prim_iUnion_balls`), hence the upper half plane
  (`exists_prim_upperHalfPlane`);
* unions `V ∪ W` of two open sets with preconnected nonempty intersection (`exists_prim_union`),
  hence `{Im z > 0} ∪ B(c, δ)` (`exists_prim_upper_union_ball`): the region where the integrand
  `G_n = R_n k⁗` is holomorphic around the certified contour, which starts at the real point
  `c ≈ n x_c`.

With a primitive, line integrals along segments are differences of the primitive
(`integral_line_eq_sub`), and the vertical ray from `v₀` can be replaced by a polyline
`v₀, v₁, …, v_K` followed by the vertical ray from `v_K` (`ray_eq_polyline_add_ray`), provided `F`
is small on the horizontal connecting segments at large height.
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

namespace ZetaIrr.Analytic

open Complex Set Metric Filter Topology MeasureTheory

/-- Two primitives of the same function on a preconnected open set that agree at one point agree
everywhere on it. -/
lemma eqOn_of_hasDerivAt {F P Q : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hs' : IsPreconnected s)
    (hP : ∀ z ∈ s, HasDerivAt P (F z) z) (hQ : ∀ z ∈ s, HasDerivAt Q (F z) z) {x : ℂ}
    (hx : x ∈ s) (hx' : P x = Q x) : EqOn P Q s :=
  hs.eqOn_of_deriv_eq hs' (fun z hz => (hP z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hQ z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [(hP z hz).deriv, (hQ z hz).deriv]) hx hx'

/-- **Primitive on a nested union of discs.** -/
theorem exists_prim_iUnion_balls {F : ℂ → ℂ} (B : ℕ → ℂ) (r : ℕ → ℝ)
    (hmono : ∀ k, ball (B k) (r k) ⊆ ball (B (k + 1)) (r (k + 1)))
    (hF : ∀ k, DifferentiableOn ℂ F (ball (B k) (r k))) (z₀ : ℂ) (hz₀ : z₀ ∈ ball (B 0) (r 0)) :
    ∃ P : ℂ → ℂ, ∀ z ∈ ⋃ k, ball (B k) (r k), HasDerivAt P (F z) z := by
  classical
  have hmono' : Monotone (fun k => ball (B k) (r k)) := monotone_nat_of_le_succ hmono
  choose g hg0 hg using fun k => ((hF k).isExactOn_ball).with_val_at z₀ 0
  have hagree : ∀ k j, k ≤ j → EqOn (g k) (g j) (ball (B k) (r k)) := by
    intro k j hkj
    exact eqOn_of_hasDerivAt isOpen_ball (convex_ball _ _).isPreconnected (hg k)
      (fun z hz => hg j z (hmono' hkj hz)) (hmono' (Nat.zero_le k) hz₀) (by rw [hg0, hg0])
  let P : ℂ → ℂ := fun z => if h : ∃ k, z ∈ ball (B k) (r k) then g (Nat.find h) z else 0
  refine ⟨P, fun z hz => ?_⟩
  have h : ∃ k, z ∈ ball (B k) (r k) := mem_iUnion.1 hz
  set k := Nat.find h
  have hzk : z ∈ ball (B k) (r k) := Nat.find_spec h
  have heq : P =ᶠ[𝓝 z] g k := by
    filter_upwards [isOpen_ball.mem_nhds hzk] with w hw
    have hw' : ∃ k, w ∈ ball (B k) (r k) := ⟨k, hw⟩
    simp only [P, dif_pos hw']
    exact hagree _ _ (Nat.find_min' hw' hw) (Nat.find_spec hw')
  exact (hg k z hzk).congr_of_eventuallyEq heq

/-- **Primitive on the upper half plane.** -/
theorem exists_prim_upperHalfPlane {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im}) :
    ∃ P : ℂ → ℂ, ∀ z : ℂ, 0 < z.im → HasDerivAt P (F z) z := by
  let B : ℕ → ℂ := fun k => ((k : ℝ) + 1 : ℝ) * I
  let r : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hsub : ∀ k, ball (B k) (r k) ⊆ {z | 0 < z.im} := by
    intro k z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h := Complex.abs_im_le_norm (z - B k)
    have him : (z - B k).im = z.im - ((k : ℝ) + 1) := by simp [B]
    rw [him] at h
    have := (abs_lt.1 (lt_of_le_of_lt h hz)).1
    show 0 < z.im
    simp only [r] at this
    linarith
  have hmono : ∀ k, ball (B k) (r k) ⊆ ball (B (k + 1)) (r (k + 1)) := by
    intro k z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    have hBB : ‖B k - B (k + 1)‖ = 1 := by
      simp only [B]; push_cast
      rw [show ((k : ℂ) + 1) * I - ((k : ℂ) + 1 + 1) * I = -I by ring, norm_neg, Complex.norm_I]
    calc ‖z - B (k + 1)‖ = ‖(z - B k) + (B k - B (k + 1))‖ := by ring_nf
      _ ≤ ‖z - B k‖ + ‖B k - B (k + 1)‖ := norm_add_le _ _
      _ < r k + 1 := by rw [hBB]; linarith
      _ = r (k + 1) := by simp only [r]; push_cast; ring
  obtain ⟨P, hP⟩ := exists_prim_iUnion_balls B r hmono (fun k => hF.mono (hsub k)) I (by
    rw [mem_ball, dist_eq_norm]; simp [B, r])
  refine ⟨P, fun z hz => hP z (mem_iUnion.2 ?_)⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (‖z‖ ^ 2 / (2 * z.im))
  refine ⟨k, ?_⟩
  rw [mem_ball, dist_eq_norm]
  have hR : 0 < r k := by simp only [r]; positivity
  have hsq : ‖z - B k‖ ^ 2 = ‖z‖ ^ 2 - 2 * r k * z.im + r k ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp [B, r]; ring
  have hlt : ‖z‖ ^ 2 < 2 * r k * z.im := by
    have : ‖z‖ ^ 2 / (2 * z.im) < r k := by simp only [r]; linarith
    rw [div_lt_iff₀ (by positivity)] at this; linarith
  have : ‖z - B k‖ ^ 2 < r k ^ 2 := by rw [hsq]; linarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hR.le two_ne_zero).1 this

/-- **Gluing primitives** on `V ∪ W` when `V ∩ W` is preconnected and nonempty. -/
theorem exists_prim_union {F P Q : ℂ → ℂ} {V W : Set ℂ} (hV : IsOpen V) (hW : IsOpen W)
    (hVW : IsPreconnected (V ∩ W)) (hne : (V ∩ W).Nonempty)
    (hP : ∀ z ∈ V, HasDerivAt P (F z) z) (hQ : ∀ z ∈ W, HasDerivAt Q (F z) z) :
    ∃ R : ℂ → ℂ, ∀ z ∈ V ∪ W, HasDerivAt R (F z) z := by
  classical
  obtain ⟨x, hx⟩ := hne
  let Q' : ℂ → ℂ := fun z => Q z - Q x + P x
  have hQ' : ∀ z ∈ W, HasDerivAt Q' (F z) z := fun z hz =>
    ((hQ z hz).sub_const (Q x)).add_const (P x)
  have hagree : EqOn P Q' (V ∩ W) :=
    eqOn_of_hasDerivAt (hV.inter hW) hVW (fun z hz => hP z hz.1) (fun z hz => hQ' z hz.2) hx
      (by simp [Q'])
  let R : ℂ → ℂ := fun z => if z ∈ V then P z else Q' z
  refine ⟨R, fun z hz => ?_⟩
  by_cases hzV : z ∈ V
  · have heq : R =ᶠ[𝓝 z] P := by
      filter_upwards [hV.mem_nhds hzV] with w hw
      simp [R, hw]
    exact (hP z hzV).congr_of_eventuallyEq heq
  · have hzW : z ∈ W := hz.resolve_left hzV
    have heq : R =ᶠ[𝓝 z] Q' := by
      filter_upwards [hW.mem_nhds hzW] with w hw
      by_cases hwV : w ∈ V
      · simp only [R, if_pos hwV]; exact hagree ⟨hwV, hw⟩
      · simp [R, hwV]
    exact (hQ' z hzW).congr_of_eventuallyEq heq

lemma convex_upperHalf : Convex ℝ {z : ℂ | 0 < z.im} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_setOf_eq, Complex.add_im, Complex.real_smul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
  rcases ha.lt_or_eq with ha' | ha'
  · nlinarith
  · subst ha'; simp at hab; subst hab; simpa using hy

/-- **Primitive on `{Im z > 0} ∪ B(c, δ)`** for real `c`. -/
theorem exists_prim_upper_union_ball {F : ℂ → ℂ} (c δ : ℝ) (hδ : 0 < δ)
    (hF : DifferentiableOn ℂ F ({z | 0 < z.im} ∪ ball (c : ℂ) δ)) :
    ∃ P : ℂ → ℂ, ∀ z ∈ {z : ℂ | 0 < z.im} ∪ ball (c : ℂ) δ, HasDerivAt P (F z) z := by
  obtain ⟨P, hP⟩ := exists_prim_upperHalfPlane (hF.mono subset_union_left)
  obtain ⟨Q, hQ⟩ := ((hF.mono subset_union_right).isExactOn_ball)
  have hopenH : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  refine exists_prim_union hopenH isOpen_ball
    ((convex_upperHalf.inter (convex_ball _ _)).isPreconnected) ⟨(c : ℂ) + (δ / 2 : ℝ) * I, ?_, ?_⟩
    (fun z hz => hP z hz) hQ
  · show 0 < ((c : ℂ) + (δ / 2 : ℝ) * I).im
    simp; linarith
  · rw [mem_ball, dist_eq_norm]
    simp [Complex.norm_I, abs_of_pos hδ]
    linarith

/-! ### Line integrals through a primitive -/

/-- `∫_0^T F(p + y v) v dy = P(p + T v) - P(p)` if `P' = F` along the segment. -/
lemma integral_line_eq_sub {F P : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hP : ∀ z ∈ U, HasDerivAt P (F z) z) (p v : ℂ) {T : ℝ}
    (hT : 0 ≤ T) (hseg : ∀ y ∈ Icc (0 : ℝ) T, p + y * v ∈ U) :
    ∫ y in (0 : ℝ)..T, F (p + y * v) * v = P (p + T * v) - P p := by
  have hγ : ∀ y : ℝ, HasDerivAt (fun y : ℝ => p + (y : ℂ) * v) v y := by
    intro y
    simpa using ((hasDerivAt_id y).ofReal_comp.mul_const v).const_add p
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => P (p + y * v))
    (f' := fun y : ℝ => F (p + y * v) * v) (a := 0) (b := T)
    (fun y hy => by
      rw [uIcc_of_le hT] at hy
      exact (hP _ (hseg y hy)).comp y (hγ y))
    (by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hT]
      refine ContinuousOn.mul ?_ continuousOn_const
      intro y hy
      exact (ContinuousAt.comp (g := F) (f := fun y : ℝ => p + (y : ℂ) * v)
        (hF.continuousOn.continuousAt (hU.mem_nhds (hseg y hy)))
        (hγ y).continuousAt).continuousWithinAt)
  simpa using h

/-- The integral of `F` along the segment `[a, b]`, parametrised by `[0, 1]`. -/
noncomputable def segInt (F : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, F (a + t * (b - a)) * (b - a)

/-- **Deformation of a vertical ray to a polyline plus a vertical ray.** Let `P` be a primitive of
`F` on an open set `U` containing the vertical rays from `v 0` and `v K`, the polyline
`v 0, …, v K`, and (for large `Y`) the horizontal segments joining the two rays at height
`Im (v 0) + Y`, on which `‖F‖ ≤ ε(Y) → 0`. Then

    i ∫_0^∞ F(v₀ + iy) dy = Σ_{k<K} ∫_{[v_k, v_{k+1}]} F + i ∫_0^∞ F(v_K + iy) dy. -/
theorem ray_eq_polyline_add_ray {F P : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hP : ∀ z ∈ U, HasDerivAt P (F z) z) (v : ℕ → ℂ) (K : ℕ)
    (hseg : ∀ k < K, ∀ t ∈ Icc (0 : ℝ) 1, v k + t * (v (k + 1) - v k) ∈ U)
    (hray0 : ∀ y : ℝ, 0 ≤ y → v 0 + y * I ∈ U) (hrayK : ∀ y : ℝ, 0 ≤ y → v K + y * I ∈ U)
    (hint0 : IntegrableOn (fun y : ℝ => F (v 0 + y * I)) (Ioi 0))
    (hintK : IntegrableOn (fun y : ℝ => F (v K + y * I)) (Ioi 0))
    (ε : ℝ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hhor : ∀ᶠ Y : ℝ in atTop, ∀ t ∈ Icc (0 : ℝ) 1,
      v 0 + Y * I + t * (((v K).re - (v 0).re : ℝ) : ℂ) ∈ U ∧
      ‖F (v 0 + Y * I + t * (((v K).re - (v 0).re : ℝ) : ℂ))‖ ≤ ε Y) :
    I * ∫ y in Ioi (0 : ℝ), F (v 0 + y * I)
      = (∑ k ∈ Finset.range K, segInt F (v k) (v (k + 1)))
        + I * ∫ y in Ioi (0 : ℝ), F (v K + y * I) := by
  set h := (v K).im - (v 0).im with hh
  set d : ℝ := (v K).re - (v 0).re with hd
  -- the polyline telescopes
  have hpoly : ∑ k ∈ Finset.range K, segInt F (v k) (v (k + 1)) = P (v K) - P (v 0) := by
    rw [← Finset.sum_range_sub (fun k => P (v k)) K]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    unfold segInt
    have := integral_line_eq_sub hU hF hP (v k) (v (k + 1) - v k) zero_le_one
      (fun t ht => hseg k (Finset.mem_range.1 hk) t ht)
    rw [this]; congr 2; push_cast; ring
  -- finite rays
  have hA : ∀ Y : ℝ, 0 ≤ Y → (∫ y in (0 : ℝ)..Y, F (v 0 + y * I)) * I
      = P (v 0 + Y * I) - P (v 0) := by
    intro Y hY
    rw [← intervalIntegral.integral_mul_const]
    exact integral_line_eq_sub hU hF hP (v 0) I hY (fun y hy => hray0 y hy.1)
  have hB : ∀ Y : ℝ, 0 ≤ Y → (∫ y in (0 : ℝ)..Y, F (v K + y * I)) * I
      = P (v K + Y * I) - P (v K) := by
    intro Y hY
    rw [← intervalIntegral.integral_mul_const]
    exact integral_line_eq_sub hU hF hP (v K) I hY (fun y hy => hrayK y hy.1)
  -- horizontal segment
  have hH : ∀ᶠ Y : ℝ in atTop, P (v K + (Y - h) * I) - P (v 0 + Y * I)
      = ∫ t in (0 : ℝ)..1, F (v 0 + Y * I + t * (d : ℂ)) * (d : ℂ) := by
    filter_upwards [hhor] with Y hY
    have e : v 0 + Y * I + (1 : ℝ) * (d : ℂ) = v K + (Y - h) * I := by
      apply Complex.ext <;> simp [hd, hh]; ring
    rw [integral_line_eq_sub hU hF hP (v 0 + Y * I) (d : ℂ) zero_le_one
      (fun t ht => (hY t ht).1), e]
  have hHlim : Tendsto (fun Y : ℝ => ∫ t in (0 : ℝ)..1, F (v 0 + Y * I + t * (d : ℂ)) * (d : ℂ))
      atTop (𝓝 0) := by
    have hb : ∀ᶠ Y : ℝ in atTop,
        ‖∫ t in (0 : ℝ)..1, F (v 0 + Y * I + t * (d : ℂ)) * (d : ℂ)‖ ≤ ε Y * |d| := by
      filter_upwards [hhor] with Y hY
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
        (C := ε Y * |d|) (f := fun t : ℝ => F (v 0 + Y * I + t * (d : ℂ)) * (d : ℂ))
        (fun t ht => by
          rw [uIoc_of_le zero_le_one] at ht
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hY t (Ioc_subset_Icc_self ht)).2 (abs_nonneg _))
      simpa using this
    refine squeeze_zero_norm' hb ?_
    simpa using hε.mul_const |d|
  -- limits of the rays
  have hlimA : Tendsto (fun Y : ℝ => (∫ y in (0 : ℝ)..Y, F (v 0 + y * I)) * I) atTop
      (𝓝 ((∫ y in Ioi (0 : ℝ), F (v 0 + y * I)) * I)) :=
    (intervalIntegral_tendsto_integral_Ioi 0 hint0 tendsto_id).mul_const I
  have hlimB : Tendsto (fun Y : ℝ => (∫ y in (0 : ℝ)..(Y - h), F (v K + y * I)) * I) atTop
      (𝓝 ((∫ y in Ioi (0 : ℝ), F (v K + y * I)) * I)) :=
    (intervalIntegral_tendsto_integral_Ioi 0 hintK
      (tendsto_atTop_add_const_right _ (-h) tendsto_id)).mul_const I
  -- combine: A(Y) - poly - B(Y) = -H(Y)
  have hcomb := (hlimA.sub (tendsto_const_nhds (x := P (v K) - P (v 0)))).sub hlimB
  have hcomb' : Tendsto (fun Y : ℝ => ((∫ y in (0 : ℝ)..Y, F (v 0 + y * I)) * I
      - (P (v K) - P (v 0))) - (∫ y in (0 : ℝ)..(Y - h), F (v K + y * I)) * I) atTop (𝓝 0) := by
    have : Tendsto (fun Y : ℝ => -∫ t in (0 : ℝ)..1, F (v 0 + Y * I + t * (d : ℂ)) * (d : ℂ))
        atTop (𝓝 0) := by simpa using hHlim.neg
    refine this.congr' ?_
    filter_upwards [hH, eventually_ge_atTop (max 0 h)] with Y hY hY0
    rw [hA Y (le_of_max_le_left hY0), hB (Y - h) (by linarith [le_of_max_le_right hY0]), ← hY]
    push_cast
    ring
  have := tendsto_nhds_unique hcomb hcomb'
  rw [hpoly]
  linear_combination this

end ZetaIrr.Analytic
