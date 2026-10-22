/-
# Coefficient valuations of power series (PROOF_BETA §3, Lemma A: the binomial argument)

`psge p e λ f` says: every coefficient satisfies `v_p([X^M] f) ≥ e - λ M`.

* `psge_mul`, `psge_prod`, `psge_pow`, `psge_listProd`: the bound is multiplicative (for a common
  slope `λ`), which is the Gauss-lemma form of the binomial argument.
* `psge_lin`: a linear factor `C u + C c X` satisfies `psge e λ` as soon as
  `v_p(u) ≥ e` (or `u = 0`) and `v_p(c) ≥ e - λ`. With `u = 0` this is the "shift `M → M-1`" of
  Lemma A for the e-factor.
* `psge_inv`: a pole factor `(C d + X)⁻¹`, `d ≠ 0`, satisfies `psge e λ` under
  precisely `e ≤ -v_p(d)` and `v_p(d) ≤ λ`. Its coefficients are `(-1)^M d^{-(M+1)}`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Arith.Valuation
import Mathlib.RingTheory.PowerSeries.Inverse

set_option linter.unusedSectionVars false

namespace ZetaIrr.Arith

open Finset PowerSeries

/-- Every coefficient `[X^M] f` has `p`-adic valuation `≥ e - λ M`. -/
def psge (p : ℕ) (e lam : ℤ) (f : PowerSeries ℚ) : Prop :=
  ∀ M : ℕ, vge p (e - lam * M) (coeff M f)

variable {p : ℕ} [hp : Fact p.Prime]

theorem psge_mono {f : PowerSeries ℚ} {e e' lam lam' : ℤ} (h : psge p e lam f) (he : e' ≤ e)
    (hl : lam ≤ lam') : psge p e' lam' f := fun M =>
  vge_mono (h M) (by nlinarith [(Nat.cast_nonneg M : (0 : ℤ) ≤ M)])

theorem psge_coeff {f : PowerSeries ℚ} {e lam : ℤ} (h : psge p e lam f) (M : ℕ) :
    vge p (e - lam * M) (coeff M f) := h M

theorem psge_mul {f g : PowerSeries ℚ} {e₁ e₂ lam : ℤ} (hf : psge p e₁ lam f)
    (hg : psge p e₂ lam g) : psge p (e₁ + e₂) lam (f * g) := by
  intro M
  rw [coeff_mul]
  refine vge_sum _ _ (fun x hx => ?_)
  have hx' : x.1 + x.2 = M := mem_antidiagonal.mp hx
  have := vge_mul (hf x.1) (hg x.2)
  refine vge_mono this (le_of_eq ?_)
  rw [← hx']; push_cast; ring

theorem psge_one (lam : ℤ) : psge p 0 lam (1 : PowerSeries ℚ) := by
  intro M
  rw [coeff_one]
  split_ifs with h
  · subst h; simpa using vge_one (p := p)
  · exact vge_zero _

theorem psge_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) (e : ι → ℤ) (lam : ℤ)
    (h : ∀ i ∈ s, psge p (e i) lam (f i)) : psge p (∑ i ∈ s, e i) lam (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using psge_one (p := p) lam
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact psge_mul (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem psge_pow {f : PowerSeries ℚ} {e lam : ℤ} (h : psge p e lam f) (n : ℕ) :
    psge p (n * e) lam (f ^ n) := by
  induction n with
  | zero => simpa using psge_one (p := p) lam
  | succ n ih =>
    rw [pow_succ]
    have := psge_mul ih h
    convert this using 1
    push_cast; ring

theorem psge_listProd {ι : Type*} (l : List ι) (f : ι → PowerSeries ℚ) (e : ι → ℤ) (lam : ℤ)
    (h : ∀ i ∈ l, psge p (e i) lam (f i)) : psge p (l.map e).sum lam (l.map f).prod := by
  induction l with
  | nil => simpa using psge_one (p := p) lam
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact psge_mul (h a List.mem_cons_self) (ih fun i hi => h i (List.mem_cons_of_mem a hi))

/-- A linear factor `C u + C c · X`. -/
theorem psge_lin {u c : ℚ} {e lam : ℤ} (hu : vge p e u) (hc : vge p (e - lam) c) :
    psge p e lam (C u + C c * X) := by
  intro M
  rw [map_add, coeff_C, coeff_C_mul, coeff_X]
  rcases M with _ | _ | M
  · simpa using hu
  · simpa using hc
  · simpa using vge_zero (p := p) _

theorem psge_C {u : ℚ} {e lam : ℤ} (hu : vge p e u) : psge p e lam (C u) := by
  have := psge_lin (p := p) (c := 0) (lam := lam) hu (vge_zero _)
  simpa using this

/-- The coefficients of `(C d + X)⁻¹`. -/
theorem inv_C_add_X_eq {d : ℚ} (hd : d ≠ 0) :
    (C d + X : PowerSeries ℚ)⁻¹ = mk fun M => (-1) ^ M * (d⁻¹) ^ (M + 1) := by
  rw [inv_eq_iff_mul_eq_one (by simp [hd])]
  ext M
  rw [mul_add, coeff_one]
  rcases M with _ | M
  · simp [hd]
  · rw [map_add, coeff_mul_C, coeff_succ_mul_X]
    simp only [coeff_mk, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    rw [pow_succ, pow_succ]
    field_simp
    ring

/-- A pole factor `(C d + X)⁻¹`, `d ≠ 0`. -/
theorem psge_inv {d : ℚ} (hd : d ≠ 0) {e lam : ℤ} (he : e ≤ -padicValRat p d)
    (hl : padicValRat p d ≤ lam) : psge p e lam (C d + X)⁻¹ := by
  intro M
  rw [inv_C_add_X_eq hd, coeff_mk]
  have h1 := vge_mul (vge_neg_one_pow (p := p) M) (vge_pow (vge_inv_self (p := p) d) (M + 1))
  refine vge_mono h1 ?_
  have hM : (0 : ℤ) ≤ M := Nat.cast_nonneg M
  push_cast
  nlinarith

end ZetaIrr.Arith
