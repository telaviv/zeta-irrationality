/-
# Second derivatives through logarithmic derivatives

`LD f U t₀ M`: on the set `U`, `f' = f · g` for some `g` which is differentiable at `t₀` with
`|g(t₀)| ≤ M` and `|g'(t₀)| ≤ M`. Then (`LD.abs_deriv2_le`), if `U` is open and `t₀ ∈ U`,

  `|f''(t₀)| = |f(t₀)| · |g(t₀)² + g'(t₀)| ≤ |f(t₀)| (M² + M)`.

The class is closed under products, quotients, powers, finite products and list products
(the bounds add), and contains affine functions `αt + β` with `|α| ≤ |αt₀ + β|` (bound `1`).
For a rational function `R = Π (t - w)^{μ_w}` with all `|t₀ - w| ≥ 1` this gives
`|R''(t₀)| ≤ |R(t₀)| (M² + M)` with `M = Σ |μ_w|`.
Status: complete (no `sorry`).
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace ZetaIrr.Size

open Set Filter Topology

/-- Logarithmic-derivative data with bound `M` at `t₀`, valid on `U`. -/
def LD (f : ℝ → ℝ) (U : Set ℝ) (t₀ M : ℝ) : Prop :=
  ∃ g g' : ℝ → ℝ, (∀ t ∈ U, HasDerivAt f (f t * g t) t) ∧ HasDerivAt g (g' t₀) t₀ ∧
    |g t₀| ≤ M ∧ |g' t₀| ≤ M

namespace LD

variable {U : Set ℝ} {t₀ : ℝ}

lemma mono {f : ℝ → ℝ} {M M' : ℝ} (h : LD f U t₀ M) (hM : M ≤ M') : LD f U t₀ M' := by
  obtain ⟨g, g', h1, h2, h3, h4⟩ := h
  exact ⟨g, g', h1, h2, h3.trans hM, h4.trans hM⟩

lemma of_eq {f f' : ℝ → ℝ} {M : ℝ} (h : LD f U t₀ M) (e : ∀ t, f t = f' t) : LD f' U t₀ M := by
  have : f = f' := funext e
  subst this; exact h

lemma const (c : ℝ) : LD (fun _ => c) U t₀ 0 :=
  ⟨fun _ => 0, fun _ => 0, fun t _ => by simpa using hasDerivAt_const t c,
    hasDerivAt_const t₀ 0, by simp, by simp⟩

lemma mul {f h : ℝ → ℝ} {M₁ M₂ : ℝ} (hf : LD f U t₀ M₁) (hh : LD h U t₀ M₂) :
    LD (fun t => f t * h t) U t₀ (M₁ + M₂) := by
  obtain ⟨g₁, g₁', a1, a2, a3, a4⟩ := hf
  obtain ⟨g₂, g₂', b1, b2, b3, b4⟩ := hh
  refine ⟨fun t => g₁ t + g₂ t, fun t => g₁' t + g₂' t, fun t ht => ?_, HasDerivAt.fun_add a2 b2, ?_, ?_⟩
  · exact ((a1 t ht).fun_mul (b1 t ht)).congr_deriv (by ring)
  · exact (abs_add_le _ _).trans (add_le_add a3 b3)
  · exact (abs_add_le _ _).trans (add_le_add a4 b4)

lemma div {f h : ℝ → ℝ} {M₁ M₂ : ℝ} (hf : LD f U t₀ M₁) (hh : LD h U t₀ M₂)
    (hne : ∀ t ∈ U, h t ≠ 0) :
    LD (fun t => f t / h t) U t₀ (M₁ + M₂) := by
  obtain ⟨g₁, g₁', a1, a2, a3, a4⟩ := hf
  obtain ⟨g₂, g₂', b1, b2, b3, b4⟩ := hh
  refine ⟨fun t => g₁ t - g₂ t, fun t => g₁' t - g₂' t, fun t ht => ?_, HasDerivAt.fun_sub a2 b2, ?_, ?_⟩
  · refine ((a1 t ht).div (b1 t ht) (hne t ht)).congr_deriv ?_
    have := hne t ht
    field_simp
  · exact (abs_sub _ _).trans (add_le_add a3 b3)
  · exact (abs_sub _ _).trans (add_le_add a4 b4)

lemma pow {f : ℝ → ℝ} {M : ℝ} (hf : LD f U t₀ M) (k : ℕ) :
    LD (fun t => f t ^ k) U t₀ (k * M) := by
  obtain ⟨g, g', a1, a2, a3, a4⟩ := hf
  refine ⟨fun t => k * g t, fun t => k * g' t, fun t ht => ?_, a2.const_mul _, ?_, ?_⟩
  · refine ((a1 t ht).pow k).congr_deriv ?_
    rcases k with _ | k
    · simp
    · simp only [Nat.add_sub_cancel]; push_cast; ring
  · rw [abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_left a3 (Nat.cast_nonneg k)
  · rw [abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_left a4 (Nat.cast_nonneg k)

lemma finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ → ℝ) {M : ℝ}
    (hf : ∀ i ∈ s, LD (f i) U t₀ M) :
    LD (fun t => ∏ i ∈ s, f i t) U t₀ (s.card * M) := by
  induction s using Finset.induction_on with
  | empty => simpa using const (U := U) (t₀ := t₀) 1
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := h1.mul h2
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine this.mono (le_of_eq ?_)
    push_cast; ring

lemma list_prod {ι : Type*} (l : List ι) (f : ι → ℝ → ℝ) (M : ι → ℝ)
    (hf : ∀ i ∈ l, LD (f i) U t₀ (M i)) :
    LD (fun t => (l.map (fun i => f i t)).prod) U t₀ (l.map M).sum := by
  induction l with
  | nil => simpa using const (U := U) (t₀ := t₀) 1
  | cons a l ih =>
    have h1 := hf a (by simp)
    have h2 := ih (fun i hi => hf i (by simp [hi]))
    simpa using h1.mul h2

/-- Affine factors `α t + β` (nonvanishing on `U`, with `|α| ≤ |α t₀ + β|`) have bound `1`. -/
lemma affine (α β : ℝ) (hne : ∀ t ∈ U, α * t + β ≠ 0) (ht₀ : t₀ ∈ U)
    (hb : |α| ≤ |α * t₀ + β|) :
    LD (fun t => α * t + β) U t₀ 1 := by
  have h0 := hne t₀ ht₀
  have hpos : 0 < |α * t₀ + β| := abs_pos.mpr h0
  refine ⟨fun t => α / (α * t + β), fun t => -(α * α) / (α * t + β) ^ 2, fun t ht => ?_, ?_, ?_, ?_⟩
  · have hl : HasDerivAt (fun t => α * t + β) α t := by
      simpa using HasDerivAt.fun_add ((hasDerivAt_id t).const_mul α) (hasDerivAt_const t β)
    refine hl.congr_deriv ?_
    field_simp [hne t ht]
  · have hl : HasDerivAt (fun t => α * t + β) α t₀ := by
      simpa using HasDerivAt.fun_add ((hasDerivAt_id t₀).const_mul α) (hasDerivAt_const t₀ β)
    have := (hl.inv h0).const_mul α
    refine (this.congr_of_eventuallyEq (Eventually.of_forall (fun t => by
      simp [div_eq_mul_inv]))).congr_deriv ?_
    field_simp
  · rw [abs_div, div_le_one hpos]; exact hb
  · rw [abs_div, abs_neg, abs_mul, abs_pow, div_le_one (by positivity)]
    calc |α| * |α| ≤ |α * t₀ + β| * |α * t₀ + β| := mul_le_mul hb hb (abs_nonneg _) (abs_nonneg _)
      _ = |α * t₀ + β| ^ 2 := by ring

/-- **The second-derivative bound.** -/
lemma abs_deriv2_le {f : ℝ → ℝ} {M : ℝ} (h : LD f U t₀ M) (hU : IsOpen U) (ht₀ : t₀ ∈ U) :
    |deriv (deriv f) t₀| ≤ |f t₀| * (M ^ 2 + M) := by
  obtain ⟨g, g', h1, h2, h3, h4⟩ := h
  have heq : deriv f =ᶠ[𝓝 t₀] fun t => f t * g t := by
    filter_upwards [hU.mem_nhds ht₀] with t ht using (h1 t ht).deriv
  rw [heq.deriv_eq]
  have hd := ((h1 t₀ ht₀).fun_mul h2).deriv
  rw [hd]
  have hM : 0 ≤ M := (abs_nonneg _).trans h3
  have e : f t₀ * g t₀ * g t₀ + f t₀ * g' t₀ = f t₀ * (g t₀ ^ 2 + g' t₀) := by ring
  rw [e, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc |g t₀ ^ 2 + g' t₀| ≤ |g t₀ ^ 2| + |g' t₀| := abs_add_le _ _
    _ = |g t₀| ^ 2 + |g' t₀| := by rw [abs_pow]
    _ ≤ M ^ 2 + M := by gcongr

end LD

end ZetaIrr.Size
