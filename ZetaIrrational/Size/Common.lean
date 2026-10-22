/-
# Generic lemmas for the real-axis size bound

Instance-independent tools used by `I3/Size/`:
* `F(y) = y log y` and its convexity (`F_tangent`), derivatives of list sums;
* `log_blk_ge`, the lower bound for one pole block;
* series enclosures of `log` (`log_series_bounds`, `log_decomp`), used by the generated `PhiNum`;
* `deriv2_cube_mul_eq_zero`: a triple zero kills the second derivative;
* the summable weight `wt t = 1/((t+1)(t+2))`.

Status: complete (no `sorry`).
-/
import Mathlib

namespace ZetaIrr.Size

open Real Finset Filter Topology

/-! ### `F(y) = y log y` and list sums -/

/-- `F(y) = y log y`. -/
noncomputable def F (y : ℝ) : ℝ := y * Real.log y

lemma continuous_F : Continuous F := Real.continuous_mul_log

lemma hasDerivAt_F {y : ℝ} (hy : y ≠ 0) : HasDerivAt F (Real.log y + 1) y :=
  Real.hasDerivAt_mul_log hy

/-- Tangent-line bound (convexity of `F`): `F y ≥ F y₀ + (log y₀ + 1)(y - y₀)` for `y ≥ 0 < y₀`. -/
lemma F_tangent {y y₀ : ℝ} (hy : 0 ≤ y) (hy₀ : 0 < y₀) :
    F y₀ + (Real.log y₀ + 1) * (y - y₀) ≤ F y := by
  unfold F
  rcases hy.eq_or_lt with h | h
  · subst h; nlinarith
  · have h1 : 1 - (y / y₀)⁻¹ ≤ Real.log (y / y₀) := Real.one_sub_inv_le_log_of_pos (by positivity)
    rw [Real.log_div h.ne' hy₀.ne', inv_div] at h1
    have h2 : y * (1 - y₀ / y) ≤ y * (Real.log y - Real.log y₀) :=
      mul_le_mul_of_nonneg_left h1 h.le
    have h3 : y * (1 - y₀ / y) = y - y₀ := by field_simp
    nlinarith

lemma hasDerivAt_list_sum {ι : Type*} (l : List ι) (f f' : ι → ℝ → ℝ) (x : ℝ)
    (h : ∀ b ∈ l, HasDerivAt (f b) (f' b x) x) :
    HasDerivAt (fun y => (l.map (fun b => f b y)).sum) ((l.map (fun b => f' b x)).sum) x := by
  induction l with
  | nil => simpa using hasDerivAt_const x (0 : ℝ)
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih (fun b hb => h b (by simp [hb])))

lemma list_sum_le {ι : Type*} (l : List ι) (f g : ι → ℝ) (h : ∀ b ∈ l, f b ≤ g b) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

/-- The lower bound `log(x+1-δ) - log(x+δ) ≥ (1-2δ)/(x+1-δ)`. -/
lemma log_blk_ge {x δ : ℝ} (h1 : 0 < x + 1 - δ) (h2 : 0 < x + δ) :
    (1 - 2 * δ) / (x + 1 - δ) ≤ Real.log (x + 1 - δ) - Real.log (x + δ) := by
  have := Real.one_sub_inv_le_log_of_pos (div_pos h1 h2)
  rw [Real.log_div h1.ne' h2.ne', inv_div] at this
  have e : 1 - (x + δ) / (x + 1 - δ) = (1 - 2 * δ) / (x + 1 - δ) := by
    field_simp; ring
  linarith

/-! ### Enclosures of `log` -/

/-- Series enclosure of `log z` for `|1 - z| < 1` (n terms). -/
lemma log_series_bounds (z : ℝ) (n : ℕ) (hx : |1 - z| < 1) :
    -(∑ i ∈ Finset.range n, (1 - z) ^ (i + 1) / (i + 1)) - |1 - z| ^ (n + 1) / (1 - |1 - z|)
      ≤ Real.log z ∧
    Real.log z ≤
      -(∑ i ∈ Finset.range n, (1 - z) ^ (i + 1) / (i + 1)) + |1 - z| ^ (n + 1) / (1 - |1 - z|) := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [sub_sub_cancel] at h
  have := abs_le.mp h
  constructor <;> linarith [this.1, this.2]

/-- `y · 2^a₂ 3^b₂ 5^c₂ = 2^a₁ 3^b₁ 5^c₁ · z` gives `log y` in terms of `log 2, log 3, log 5, log z`. -/
lemma log_decomp (y z : ℝ) (a₁ a₂ b₁ b₂ c₁ c₂ : ℕ) (hy : 0 < y) (hz : 0 < z)
    (h : y * (2 ^ a₂ * 3 ^ b₂ * 5 ^ c₂) = 2 ^ a₁ * 3 ^ b₁ * 5 ^ c₁ * z) :
    Real.log y = ((a₁ : ℝ) - a₂) * Real.log 2 + ((b₁ : ℝ) - b₂) * Real.log 3 +
      ((c₁ : ℝ) - c₂) * Real.log 5 + Real.log z := by
  have h1 := congrArg Real.log h
  rw [Real.log_mul hy.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hz.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow] at h1
  linarith

/-! ### Linearity of weighted list sums -/

lemma list_sum_lin {ι : Type*} (l : List ι) (w f g : ι → ℝ) (α β γ : ℝ) :
    (l.map (fun b => w b * (α * f b + β * g b + γ))).sum =
      α * (l.map (fun b => w b * f b)).sum + β * (l.map (fun b => w b * g b)).sum +
        γ * (l.map w).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-! ### Triple zeros and the second derivative -/

lemma contDiff_list_prod {ι : Type*} (l : List ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ l, ContDiff ℝ 2 (f i)) :
    ContDiff ℝ 2 (fun t => (l.map (fun i => f i t)).prod) := by
  induction l with
  | nil => simpa using contDiff_const
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi])))

lemma deriv2_cube_mul_eq_zero {h : ℝ → ℝ} {U : Set ℝ} {a : ℝ} (hU : IsOpen U) (ha : a ∈ U)
    (hh : ContDiffOn ℝ 2 h U) : deriv (deriv (fun t => (t - a) ^ 3 * h t)) a = 0 := by
  have hd : ∀ t ∈ U, DifferentiableAt ℝ h t := fun t ht =>
    ((hh t ht).contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num)
  have hc : ∀ t, HasDerivAt (fun t => (t - a) ^ 3) (3 * (t - a) ^ 2) t := by
    intro t
    have := ((hasDerivAt_id t).sub_const a).fun_pow 3
    simpa using this
  have heq : deriv (fun t => (t - a) ^ 3 * h t) =ᶠ[𝓝 a]
      fun t => 3 * (t - a) ^ 2 * h t + (t - a) ^ 3 * deriv h t := by
    filter_upwards [hU.mem_nhds ha] with t ht
    exact ((hc t).fun_mul (hd t ht).hasDerivAt).deriv
  rw [heq.deriv_eq]
  have hd2 : DifferentiableAt ℝ (deriv h) a :=
    (((hh.deriv_of_isOpen hU (m := 1) (by norm_num)) a ha).contDiffAt
      (hU.mem_nhds ha)).differentiableAt (by norm_num)
  have hc2 : HasDerivAt (fun t => 3 * (t - a) ^ 2) (3 * (2 * (a - a))) a := by
    have := (((hasDerivAt_id a).sub_const a).fun_pow 2).const_mul 3
    simpa using this
  have H := ((hc2.fun_mul (hd a ha).hasDerivAt).fun_add ((hc a).fun_mul hd2.hasDerivAt))
  rw [H.deriv]
  simp

/-! ### The summable weight -/

/-- The summable weight `w(t) = 1/((t+1)(t+2))`. -/
noncomputable def wt (t : ℕ) : ℝ := 1 / (((t : ℝ) + 1) * ((t : ℝ) + 2))

lemma wt_nonneg (t : ℕ) : 0 ≤ wt t := by unfold wt; positivity

lemma sum_range_wt (N : ℕ) : ∑ t ∈ range N, wt t = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    unfold wt
    push_cast
    field_simp
    ring

lemma sum_range_wt_le (N : ℕ) : ∑ t ∈ range N, wt t ≤ 1 := by
  rw [sum_range_wt]
  have : 0 < 1 / ((N : ℝ) + 1) := by positivity
  linarith

lemma summable_wt : Summable wt := summable_of_sum_range_le wt_nonneg sum_range_wt_le

lemma tsum_wt_le : ∑' t, wt t ≤ 1 := Real.tsum_le_of_sum_range_le wt_nonneg sum_range_wt_le

end ZetaIrr.Size
