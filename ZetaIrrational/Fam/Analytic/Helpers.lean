/-
# Instance-independent helpers for the analytic part of Lemma 6

* `Gamma_add_nat_eq_mul_prod`: `Γ(w + k) = Γ(w) Π_{j<k} (w + j)`;
* list products of casts and inverses (`list_prod_map_ofReal`, `list_prod_map_inv`);
* block-product reorganisation (`prod_list_blocks`, `sum_list_blocks`);
* small norm bounds: `norm_exp_le_three`, `norm_log_le_of_ge`, `norm_exp_two_pi_I_mul`.
-/
import ZetaIrrational.Analytic.Laplace
import ZetaIrrational.Analytic.ContourCommon
import ZetaIrrational.Stirling.All
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace ZetaIrr.Fam.Analytic

open Complex Real Finset Filter Topology Metric
open ZetaIrr.Analytic (norm_cexp_sub_one_le_mul_exp)

/-! ### Γ-products (from `Analytic/GammaFactor.lean`) -/

/-- `Γ(w + k) = Γ(w) Π_{j<k} (w + j)` for `w ∉ {0, -1, -2, …}`. -/
lemma Gamma_add_nat_eq_mul_prod (w : ℂ) (hw : ∀ k : ℕ, w ≠ -k) (k : ℕ) :
    Complex.Gamma (w + k) = Complex.Gamma w * ∏ j ∈ range k, (w + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hne : w + k ≠ 0 := fun h => hw k (by linear_combination h)
    rw [prod_range_succ, show w + ((k + 1 : ℕ) : ℂ) = (w + k) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hne, ih]
    ring

lemma list_prod_map_ofReal {α : Type*} (l : List α) (g : α → ℝ) :
    ((l.map g).prod : ℂ) = (l.map (fun a => (g a : ℂ))).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma list_prod_map_inv {α : Type*} (l : List α) (g : α → ℂ) :
    (l.map (fun a => (g a)⁻¹)).prod = ((l.map g).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

/-! ### Block bookkeeping -/

/-- Reorganising a product of block products (general list version). -/
lemma prod_list_blocks {M : Type*} [CommMonoid M] (x : ℕ → M) (I : ℕ × ℕ → Finset ℕ)
    (U : Finset ℕ) (L : List (ℕ × ℕ)) (hsub : ∀ b ∈ L, I b ⊆ U) :
    (L.map (fun b => (∏ k ∈ I b, x k) ^ b.2)).prod
      = ∏ k ∈ U, x k ^ (L.map (fun b => if k ∈ I b then b.2 else 0)).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, Finset.prod_mul_distrib]
    rw [ih (fun b' hb' => hsub b' (List.mem_cons_of_mem _ hb'))]
    congr 1
    simp only [pow_ite, pow_zero]
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr (hsub b (List.mem_cons_self ..)),
      Finset.prod_pow]

/-- Additive version: counting with multiplicity. -/
lemma sum_list_blocks (I : ℕ × ℕ → Finset ℕ) (U : Finset ℕ) (L : List (ℕ × ℕ))
    (hsub : ∀ b ∈ L, I b ⊆ U) :
    ∑ k ∈ U, (L.map (fun b => if k ∈ I b then b.2 else 0)).sum
      = (L.map (fun b => b.2 * (I b).card)).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih (fun b' hb' => hsub b' (List.mem_cons_of_mem _ hb'))]
    congr 1
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub b (List.mem_cons_self ..)),
      Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### Conjugation symmetry and triple zeros (from `Analytic/ConcreteIntegrand.lean`) -/

/-! ### Logarithmic derivatives -/

lemma hπC : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero

/-! ### The `q`-form and amplitude helpers (from `Analytic/FnPath.lean`) -/

lemma norm_exp_le_three {e : ℂ} (he : ‖e‖ ≤ 1) : ‖Complex.exp e‖ ≤ 3 := by
  calc ‖Complex.exp e‖ ≤ Real.exp ‖e‖ := Complex.norm_exp_le_exp_norm e
    _ ≤ Real.exp 1 := Real.exp_le_exp.2 he
    _ ≤ 3 := by linarith [Real.exp_one_lt_d9]

lemma norm_log_le_of_ge {w : ℂ} {a : ℝ} (ha : 0 < a) (hw : a ≤ ‖w‖) :
    ‖Complex.log w‖ ≤ ‖w‖ + |Real.log a| + π := by
  have hw0 : 0 < ‖w‖ := lt_of_lt_of_le ha hw
  have h1 : ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 : |Complex.arg w| ≤ π := Complex.abs_arg_le_pi w
  have h3 : |Real.log ‖w‖| ≤ ‖w‖ + |Real.log a| := by
    rcases le_or_gt 1 ‖w‖ with h | h
    · rw [abs_of_nonneg (Real.log_nonneg h)]
      have := Real.log_le_sub_one_of_pos hw0
      linarith [abs_nonneg (Real.log a)]
    · rw [abs_of_neg (Real.log_neg hw0 h)]
      have : Real.log a ≤ Real.log ‖w‖ := Real.log_le_log ha hw
      have := neg_abs_le (Real.log a)
      linarith
  linarith

lemma norm_exp_two_pi_I_mul (n : ℝ) (x : ℂ) :
    ‖Complex.exp (2 * π * I * ((n : ℂ) * x))‖ = Real.exp (-(2 * π * n * x.im)) := by
  rw [Complex.norm_exp]; congr 1; simp; ring

end ZetaIrr.Fam.Analytic
