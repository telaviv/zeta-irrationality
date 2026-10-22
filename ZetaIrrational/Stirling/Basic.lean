/-
# Uniform complex Stirling: basic objects

* `kerQ t = {t}(1 - {t})/2`, the periodic kernel (`0 ≤ kerQ ≤ 1/8`, mean `1/12`);
* `SectorBound s w : ∀ t ≥ 0, s (t + ‖w‖) ≤ ‖t + w‖`, the geometric form of the sector condition,
  with `sectorBound_of_arg`: `|arg w| ≤ π - φ` gives `SectorBound (sin (φ/2)) w`;
* `Jm m w = ∫_0^∞ kerQ t / (t + w)^m dt`, integrability and the basic bound
  `‖Jm m w‖ ≤ (1/8) / (s^m (m-1) ‖w‖^(m-1))`.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.Floor

namespace ZetaIrr.Stirling

open Complex Set MeasureTheory Filter Topology

/-- The periodic kernel `Q(t) = {t}(1 - {t})/2`. -/
noncomputable def kerQ (t : ℝ) : ℝ := Int.fract t * (1 - Int.fract t) / 2

lemma kerQ_nonneg (t : ℝ) : 0 ≤ kerQ t := by
  unfold kerQ
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have : 0 ≤ Int.fract t * (1 - Int.fract t) := mul_nonneg h0 (by linarith)
  linarith

lemma kerQ_le (t : ℝ) : kerQ t ≤ 1 / 8 := by
  unfold kerQ
  nlinarith [sq_nonneg (Int.fract t - 1 / 2)]

lemma measurable_kerQ : Measurable kerQ := by
  unfold kerQ
  exact ((measurable_fract).mul (measurable_const.sub measurable_fract)).div_const _

/-- On `[k, k+1]`, `kerQ t = (t - k)(k + 1 - t)/2`. -/
lemma kerQ_eq_of_mem (k : ℕ) {t : ℝ} (ht : t ∈ Icc (k : ℝ) (k + 1)) :
    kerQ t = (t - k) * (k + 1 - t) / 2 := by
  rcases eq_or_lt_of_le ht.2 with h | h
  · subst h
    have : Int.fract ((k : ℝ) + 1) = 0 := by
      rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
      exact Int.fract_natCast _
    simp [kerQ, this]
  · have hf : Int.fract t = t - k := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith [ht.1], by linarith, k, by push_cast; ring⟩
    simp only [kerQ, hf]
    ring

/-- The geometric sector condition: `‖t + w‖ ≥ s (t + ‖w‖)` for all `t ≥ 0`. -/
def SectorBound (s : ℝ) (w : ℂ) : Prop := ∀ t : ℝ, 0 ≤ t → s * (t + ‖w‖) ≤ ‖(t : ℂ) + w‖

/-- `|arg w| ≤ π - φ` with `0 < φ ≤ π` gives `‖t + w‖ ≥ sin(φ/2) (t + ‖w‖)`. -/
theorem sectorBound_of_arg {φ : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ Real.pi) {w : ℂ}
    (hw : |arg w| ≤ Real.pi - φ) : SectorBound (Real.sin (φ / 2)) w := by
  intro t ht
  set r := ‖w‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hs0 : 0 ≤ Real.sin (φ / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
  -- cos (arg w) ≥ - cos φ
  have hcos : -Real.cos φ ≤ Real.cos (arg w) := by
    rw [← Real.cos_abs (arg w), ← Real.cos_pi_sub]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hw
  have hre : w.re = r * Real.cos (arg w) := (norm_mul_cos_arg w).symm
  have hw2 : r ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [hr, Complex.sq_norm, Complex.normSq_apply]; ring
  have hnorm2 : ‖(t : ℂ) + w‖ ^ 2 = t ^ 2 + 2 * t * w.re + r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hw2]
    simp only [add_re, ofReal_re, add_im, ofReal_im, zero_add]
    ring
  have hsin2 : Real.sin (φ / 2) ^ 2 = (1 - Real.cos φ) / 2 := by
    have := Real.cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at this
    have h2 := Real.sin_sq_add_cos_sq (φ / 2)
    linarith
  have hc1 : -1 ≤ Real.cos φ := Real.neg_one_le_cos φ
  have key : (Real.sin (φ / 2) * (t + r)) ^ 2 ≤ ‖(t : ℂ) + w‖ ^ 2 := by
    rw [hnorm2, mul_pow, hsin2, hre]
    have h1 : t * r * (-Real.cos φ) ≤ t * r * Real.cos (arg w) :=
      mul_le_mul_of_nonneg_left hcos (mul_nonneg ht hr0)
    nlinarith [mul_nonneg (show 0 ≤ 1 + Real.cos φ by linarith) (sq_nonneg (t - r))]
  exact (pow_le_pow_iff_left₀ (mul_nonneg hs0 (by linarith)) (norm_nonneg _) two_ne_zero).mp key

lemma SectorBound.add_pos {s : ℝ} (hs : 0 ≤ s) {w : ℂ} (h : SectorBound s w) {β : ℝ} (hβ : 0 ≤ β) :
    SectorBound s (w + β) := by
  intro t ht
  have h1 := h (t + β) (by linarith)
  have h2 : ‖w + β‖ ≤ ‖w‖ + β := by
    calc ‖w + β‖ ≤ ‖w‖ + ‖(β : ℂ)‖ := norm_add_le _ _
      _ = ‖w‖ + β := by rw [Complex.norm_of_nonneg hβ]
  calc s * (t + ‖w + β‖) ≤ s * (t + β + ‖w‖) := by
        apply mul_le_mul_of_nonneg_left _ hs; linarith
    _ ≤ ‖((t + β : ℝ) : ℂ) + w‖ := h1
    _ = ‖(t : ℂ) + (w + β)‖ := by push_cast; ring_nf

lemma SectorBound.smul_pos {s : ℝ} {w : ℂ} (h : SectorBound s w) {c : ℝ} (hc : 0 < c) :
    SectorBound s ((c : ℂ) * w) := by
  intro t ht
  have h1 := h (t / c) (div_nonneg ht hc.le)
  have e1 : ‖(c : ℂ) * w‖ = c * ‖w‖ := by
    rw [norm_mul, Complex.norm_of_nonneg hc.le]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e2 : (t : ℂ) + c * w = (c : ℂ) * (((t / c : ℝ) : ℂ) + w) := by
    push_cast; rw [mul_add, mul_div_cancel₀ _ hc']
  rw [e1, e2, norm_mul, Complex.norm_of_nonneg hc.le]
  have : s * (t + c * ‖w‖) = c * (s * (t / c + ‖w‖)) := by field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h1 hc.le

lemma SectorBound.norm_pos {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ≠ 0) (h : SectorBound s w)
    {t : ℝ} (ht : 0 ≤ t) : 0 < ‖(t : ℂ) + w‖ := by
  have := h t ht
  have : 0 < s * (t + ‖w‖) := mul_pos hs (by have := norm_pos_iff.mpr hw; linarith)
  linarith

lemma SectorBound.ne_zero {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ≠ 0) (h : SectorBound s w)
    {t : ℝ} (ht : 0 ≤ t) : (t : ℂ) + w ≠ 0 :=
  norm_pos_iff.mp (h.norm_pos hs hw ht)

/-- Points of the slit plane satisfy a sector bound. -/
lemma exists_sectorBound {w : ℂ} (hw : w ∈ slitPlane) : ∃ s > 0, SectorBound s w := by
  rw [mem_slitPlane_iff_arg] at hw
  have hlt : |arg w| < Real.pi := by
    rcases lt_or_eq_of_le (abs_le.mpr ⟨(neg_pi_lt_arg w).le, arg_le_pi w⟩) with h | h
    · exact h
    · exfalso
      rcases abs_eq (Real.pi_pos.le) |>.mp h with h' | h'
      · exact hw.1 h'
      · linarith [neg_pi_lt_arg w]
  refine ⟨Real.sin ((Real.pi - |arg w|) / 2), ?_, sectorBound_of_arg (by linarith)
    (by linarith [abs_nonneg (arg w)]) (by linarith)⟩
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith
  · linarith [abs_nonneg (arg w), Real.pi_pos]

lemma ofReal_add_mem_slitPlane {w : ℂ} (hw : w ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    (t : ℂ) + w ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hw ⊢
  rcases hw with h | h
  · left; simp; linarith
  · right; simpa using h

/-! ## The integrals `Jm m w` -/

/-- `Jm m w = ∫_0^∞ kerQ t / (t + w)^m dt`. -/
noncomputable def Jm (m : ℕ) (w : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), (kerQ t : ℂ) / ((t : ℂ) + w) ^ m

/-- The Stirling remainder integral `J = Jm 2`. -/
noncomputable def J (w : ℂ) : ℂ := Jm 2 w

lemma measurable_integrand (m : ℕ) (w : ℂ) :
    Measurable (fun t : ℝ => (kerQ t : ℂ) / ((t : ℂ) + w) ^ m) := by
  have h1 : Measurable (fun t : ℝ => (kerQ t : ℂ)) := measurable_ofReal.comp measurable_kerQ
  have h2 : Measurable (fun t : ℝ => ((t : ℂ) + w) ^ m) :=
    ((measurable_ofReal).add_const w).pow_const m
  exact h1.div h2

/-- `∫_0^∞ (t + r)^{-m} dt = r^{1-m}/(m-1)` for `r > 0`, `m ≥ 2`, with integrability. -/
lemma integral_inv_add_pow {r : ℝ} (hr : 0 < r) {m : ℕ} (hm : 2 ≤ m) :
    IntegrableOn (fun t : ℝ => 1 / (t + r) ^ m) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), 1 / (t + r) ^ m = 1 / ((m - 1) * r ^ (m - 1)) := by
  set g : ℝ → ℝ := fun t => -1 / ((m - 1) * (t + r) ^ (m - 1)) with hg
  have hm1 : (0 : ℝ) < m - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt g (1 / (x + r) ^ m) x := by
    intro x hx
    have hx0 : 0 < x + r := by simp at hx; linarith
    have h1 : HasDerivAt (fun t : ℝ => (m - 1) * (t + r) ^ (m - 1))
        ((m - 1) * ((m - 1 : ℕ) * (x + r) ^ (m - 1 - 1) * 1)) x :=
      (((hasDerivAt_id x).add_const r).pow (m - 1)).const_mul _
    have h2 := (h1.inv (by positivity)).const_mul (-1 : ℝ)
    convert h2 using 1
    · ext t; simp [hg, div_eq_mul_inv]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      simp only [show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega]
      push_cast at hm1 ⊢
      have hk : (k : ℝ) + 2 - 1 ≠ 0 := hm1.ne'
      have hk' : (k : ℝ) + 1 ≠ 0 := by positivity
      have hxr : x + r ≠ 0 := hx0.ne'
      field_simp
      ring
  have hlim : Tendsto g atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => (m - 1) * (t + r) ^ (m - 1)) atTop atTop := by
      apply Tendsto.const_mul_atTop hm1
      apply tendsto_pow_atTop (by omega) |>.comp
      exact tendsto_atTop_add_const_right _ r tendsto_id
    have := this.inv_tendsto_atTop.const_mul (-1)
    simpa [hg, div_eq_mul_inv] using this
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ 1 / (x + r) ^ m := by
    intro x hx; simp at hx; positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  simp only [hg, zero_add]
  ring

/-- Integrability and the basic bound for `Jm`. -/
theorem integrable_Jm {s : ℝ} (hs : 0 < s) {w : ℂ} (hw : w ≠ 0) (h : SectorBound s w) {m : ℕ}
    (hm : 2 ≤ m) :
    IntegrableOn (fun t : ℝ => (kerQ t : ℂ) / ((t : ℂ) + w) ^ m) (Ioi 0) := by
  have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨hint, -⟩ := integral_inv_add_pow hr hm
  refine Integrable.mono' (hint.const_mul ((1 / 8) / s ^ m))
    (measurable_integrand m w).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine ae_of_all _ (fun t ht => ?_)
  simp only [mem_Ioi] at ht
  have hpos := h.norm_pos hs hw ht.le
  have hb := h t ht.le
  rw [norm_div, norm_pow, Complex.norm_of_nonneg (kerQ_nonneg t)]
  have hst : 0 < s * (t + ‖w‖) := mul_pos hs (by linarith)
  calc kerQ t / ‖(t : ℂ) + w‖ ^ m ≤ (1 / 8) / (s * (t + ‖w‖)) ^ m := by
        apply div_le_div₀ (by norm_num) (kerQ_le t) (by positivity)
        exact pow_le_pow_left₀ hst.le hb m
    _ = (1 / 8) / s ^ m * (1 / (t + ‖w‖) ^ m) := by rw [mul_pow]; field_simp

end ZetaIrr.Stirling
