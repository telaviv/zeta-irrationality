/-
# p-adic valuation toolkit

`vge p b x` means `x = 0 ∨ b ≤ v_p(x)` for `x ∈ ℚ` and an integer bound `b`.

Adapted from `domino14/zeta5`, `Zeta5/Valuation.lean` and `Zeta5/MuMod.lean` (Apache-2.0), with
integer instead of rational bounds.

Main facts:
* closure of `vge` under sums, products, powers, finite sums and products;
* `int_of_forall_vge`: a rational that is `p`-integral for every prime `p` is an integer.

Status: complete (no `sorry`).
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace ZetaIrr.Arith

open Finset

/-- `x = 0` or `b ≤ v_p(x)`. -/
def vge (p : ℕ) (b : ℤ) (x : ℚ) : Prop := x ≠ 0 → b ≤ padicValRat p x

variable {p : ℕ} [hp : Fact p.Prime]

theorem vge_zero (b : ℤ) : vge p b 0 := fun h => absurd rfl h

theorem vge_mono {x : ℚ} {b b' : ℤ} (h : vge p b x) (hb : b' ≤ b) : vge p b' x :=
  fun hx => hb.trans (h hx)

theorem vge_max {x : ℚ} {b c : ℤ} (hb : vge p b x) (hc : vge p c x) : vge p (max b c) x :=
  fun hx => max_le (hb hx) (hc hx)

theorem vge_self {x : ℚ} : vge p (padicValRat p x) x := fun _ => le_rfl

theorem vge_add {x y : ℚ} {b : ℤ} (hx : vge p b x) (hy : vge p b y) : vge p b (x + y) := by
  intro hxy
  by_cases hx0 : x = 0
  · subst hx0; simpa using hy (by simpa using hxy)
  by_cases hy0 : y = 0
  · subst hy0; simpa using hx (by simpa using hxy)
  exact le_trans (le_min (hx hx0) (hy hy0)) (padicValRat.min_le_padicValRat_add (p := p) hxy)

theorem vge_neg {x : ℚ} {b : ℤ} (h : vge p b x) : vge p b (-x) := by
  intro hx
  rw [padicValRat.neg]
  exact h (neg_ne_zero.mp hx)

theorem vge_neg_iff {x : ℚ} {b : ℤ} : vge p b (-x) ↔ vge p b x :=
  ⟨fun h => by simpa using vge_neg h, vge_neg⟩

theorem vge_sub {x y : ℚ} {b : ℤ} (hx : vge p b x) (hy : vge p b y) : vge p b (x - y) := by
  rw [sub_eq_add_neg]; exact vge_add hx (vge_neg hy)

theorem vge_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {b : ℤ} (h : ∀ i ∈ s, vge p b (f i)) :
    vge p b (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vge_zero (p := p) b
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact vge_add (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem vge_mul {x y : ℚ} {a b : ℤ} (hx : vge p a x) (hy : vge p b y) : vge p (a + b) (x * y) := by
  intro hxy
  have hx0 : x ≠ 0 := left_ne_zero_of_mul hxy
  have hy0 : y ≠ 0 := right_ne_zero_of_mul hxy
  rw [padicValRat.mul hx0 hy0]
  exact add_le_add (hx hx0) (hy hy0)

theorem vge_one : vge p 0 1 := by
  intro _; simp

theorem vge_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (b : ι → ℤ)
    (h : ∀ i ∈ s, vge p (b i) (f i)) : vge p (∑ i ∈ s, b i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vge_one (p := p)
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact vge_mul (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

theorem vge_pow {x : ℚ} {b : ℤ} (h : vge p b x) (n : ℕ) : vge p (n * b) (x ^ n) := by
  induction n with
  | zero => simpa using vge_one (p := p)
  | succ n ih =>
    rw [pow_succ]
    have := vge_mul ih h
    convert this using 1
    push_cast; ring

theorem vge_int (z : ℤ) : vge p 0 (z : ℚ) := by
  intro _
  rw [padicValRat.of_int]
  exact_mod_cast Nat.zero_le _

theorem vge_nat (n : ℕ) : vge p 0 (n : ℚ) := by
  simpa using vge_int (p := p) (n : ℤ)

theorem vge_neg_one_pow (n : ℕ) : vge p 0 ((-1 : ℚ) ^ n) := by
  simpa using vge_pow (vge_int (p := p) (-1)) n

theorem vge_int_dvd {z : ℤ} (h : (p : ℤ) ∣ z) : vge p 1 (z : ℚ) := by
  intro hz
  have hz0 : z ≠ 0 := by exact_mod_cast hz
  rw [padicValRat.of_int]
  rcases (padicValInt_dvd_iff 1 z).mp (by simpa using h) with h0 | h1
  · exact absurd h0 hz0
  · exact_mod_cast h1

/-- `v_p(x⁻¹) = -v_p(x)`. -/
theorem vge_inv_self (x : ℚ) : vge p (-padicValRat p x) x⁻¹ := by
  intro _
  rw [padicValRat.inv]

theorem vge_inv {x : ℚ} {b : ℤ} (h : padicValRat p x ≤ b) : vge p (-b) x⁻¹ :=
  vge_mono (vge_inv_self x) (by omega)

/-- A `p`-integral rational has denominator prime to `p`. -/
theorem not_dvd_den_of_vge {r : ℚ} (h : vge p 0 r) : ¬ p ∣ r.den := by
  intro hd
  by_cases hr : r = 0
  · subst hr; simp at hd; exact hp.out.one_lt.ne' hd
  have hv := h hr
  have hnum : ¬ (p : ℤ) ∣ r.num := by
    intro hn
    have h1 : p ∣ r.num.natAbs := Int.natCast_dvd.mp hn
    have h2 : p ∣ Nat.gcd r.num.natAbs r.den := Nat.dvd_gcd h1 hd
    rw [r.reduced] at h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  rw [padicValRat_def, padicValInt.eq_zero_of_not_dvd hnum] at hv
  have h1 : 1 ≤ padicValNat p r.den := one_le_padicValNat_of_dvd r.den_nz hd
  omega

end ZetaIrr.Arith

namespace ZetaIrr.Arith

/-- A rational that is `p`-integral for every prime `p` is an integer. -/
theorem int_of_forall_vge {x : ℚ} (h : ∀ p : ℕ, p.Prime → vge p 0 x) : ∃ z : ℤ, (z : ℚ) = x := by
  refine ⟨x.num, ?_⟩
  have hden : x.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    haveI : Fact p.Prime := ⟨hp⟩
    exact not_dvd_den_of_vge (h p hp) hpd
  exact (Rat.den_eq_one_iff x).mp hden

end ZetaIrr.Arith
