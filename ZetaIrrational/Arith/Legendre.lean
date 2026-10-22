/-
# Legendre-type bounds for sums of `p`-adic valuations (for PROOF_BETA §4, "Size")

For a prime `p`, writing `Λ(N) = ⌊log_p N⌋`:
* `digitSum_le`: the base-`p` digit sum of `N` is `≤ (p-1)(Λ(N)+1)`;
* `legendre_lower`, `legendre_upper`: `N - (p-1)(Λ(N)+1) ≤ (p-1) v_p(N!) ≤ N`;
* `sum_Icc_padicValNat`: `Σ_{d=A}^{B} v_p(d) = v_p(B!) - v_p((A-1)!)`, and
  `sub_one_mul_sum_Icc_le`: `(p-1) Σ_{d=A}^{B} v_p(d) ≤ (B + 1 - A) + (p-1)(Λ(A-1)+1)`;
* `oddSum_add`: for odd `p`, `Σ_{j<A} v_p(2j+1) + v_p(A!) = v_p((2A)!)`, and
  `sub_one_mul_oddSum_ge`: `(p-1) Σ_{j<A} v_p(2j+1) ≥ A - (p-1)(Λ(2A)+1)`.

Status: complete (no `sorry`).
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Digits.Lemmas

set_option linter.unusedSectionVars false

namespace ZetaIrr.Arith

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

theorem digitSum_le (N : ℕ) : (p.digits N).sum ≤ (p - 1) * (Nat.log p N + 1) := by
  have h1 : ∀ d ∈ p.digits N, d ≤ p - 1 := fun d hd => by
    have := Nat.digits_lt_base hp.out.one_lt hd; omega
  have h2 := List.sum_le_length_nsmul (p.digits N) (p - 1) h1
  have h3 : (p.digits N).length ≤ Nat.log p N + 1 :=
    (Nat.digits_length_le_iff hp.out.one_lt N).mpr (Nat.lt_pow_succ_log_self hp.out.one_lt N)
  rw [smul_eq_mul] at h2
  calc (p.digits N).sum ≤ (p.digits N).length * (p - 1) := h2
    _ ≤ (Nat.log p N + 1) * (p - 1) := Nat.mul_le_mul_right _ h3
    _ = (p - 1) * (Nat.log p N + 1) := by ring

theorem legendre_eq (N : ℕ) :
    ((p - 1 : ℕ) : ℤ) * (padicValNat p N.factorial : ℤ) = N - ((p.digits N).sum : ℤ) := by
  have h := sub_one_mul_padicValNat_factorial (p := p) N
  have h2 := Nat.digit_sum_le p N
  rw [← Nat.cast_mul, h, Nat.cast_sub h2]

theorem legendre_upper (N : ℕ) :
    ((p - 1 : ℕ) : ℤ) * (padicValNat p N.factorial : ℤ) ≤ N := by
  rw [legendre_eq]; omega

theorem legendre_lower (N : ℕ) :
    (N : ℤ) - ((p - 1 : ℕ) : ℤ) * ((Nat.log p N : ℤ) + 1)
      ≤ ((p - 1 : ℕ) : ℤ) * (padicValNat p N.factorial : ℤ) := by
  rw [legendre_eq]
  have := digitSum_le (p := p) N
  have h : (((p.digits N).sum : ℕ) : ℤ) ≤ ((p - 1 : ℕ) : ℤ) * ((Nat.log p N : ℤ) + 1) := by
    exact_mod_cast this
  linarith

theorem sum_Icc_one_padicValNat (B : ℕ) :
    ∑ d ∈ Icc 1 B, padicValNat p d = padicValNat p B.factorial := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero B)]
    ring

theorem sum_Icc_padicValNat {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B + 1) :
    (∑ d ∈ Icc A B, padicValNat p d) + padicValNat p (A - 1).factorial
      = padicValNat p B.factorial := by
  rw [← sum_Icc_one_padicValNat, ← sum_Icc_one_padicValNat]
  have hsplit : Icc 1 B = Icc 1 (A - 1) ∪ Icc A B := by
    ext x; simp only [mem_union, mem_Icc]; omega
  rw [hsplit, sum_union (by
    rw [disjoint_left]; intro x h1 h2; simp only [mem_Icc] at h1 h2; omega)]
  ring

/-- `(p-1) Σ_{d=A}^{B} v_p(d) ≤ (B + 1 - A) + (p-1)(Λ(A-1)+1)` for `A ≥ 1`. -/
theorem sub_one_mul_sum_Icc_le {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B + 1) :
    ((p - 1 : ℕ) : ℤ) * ((∑ d ∈ Icc A B, padicValNat p d : ℕ) : ℤ)
      ≤ ((B : ℤ) + 1 - A) + ((p - 1 : ℕ) : ℤ) * ((Nat.log p (A - 1) : ℤ) + 1) := by
  · have h := sum_Icc_padicValNat (p := p) hA hAB
    have hu := legendre_upper (p := p) B
    have hl := legendre_lower (p := p) (A - 1)
    have h' : ((∑ d ∈ Icc A B, padicValNat p d : ℕ) : ℤ)
        = (padicValNat p B.factorial : ℤ) - (padicValNat p (A - 1).factorial : ℤ) := by
      rw [← h]; push_cast; ring
    rw [h', mul_sub]
    have hc : ((A - 1 : ℕ) : ℤ) = (A : ℤ) - 1 := by omega
    rw [hc] at hl
    linarith

/-- A cleaner form: `(p-1) Σ_{d=A}^{B} v_p(d) ≤ (B + 1 - A)_+ + (p-1)(Λ(N)+1)` whenever
`1 ≤ A` and `A - 1 ≤ N`. -/
theorem sub_one_mul_sum_Icc_le' {A B N : ℕ} (hA : 1 ≤ A) (hN : A - 1 ≤ N) :
    ((p - 1 : ℕ) : ℤ) * ((∑ d ∈ Icc A B, padicValNat p d : ℕ) : ℤ)
      ≤ ((#(Icc A B) : ℕ) : ℤ) + ((p - 1 : ℕ) : ℤ) * ((Nat.log p N : ℤ) + 1) := by
  have hlog : (Nat.log p (A - 1) : ℤ) ≤ Nat.log p N := by exact_mod_cast Nat.log_mono_right hN
  have hp1 : (0 : ℤ) ≤ ((p - 1 : ℕ) : ℤ) := by positivity
  by_cases hAB : A ≤ B + 1
  · have h := sub_one_mul_sum_Icc_le (p := p) (B := B) hA hAB
    rw [Nat.card_Icc]
    have : ((B + 1 - A : ℕ) : ℤ) = (B : ℤ) + 1 - A := by omega
    rw [this]
    nlinarith
  · have hE : Icc A B = ∅ := by ext x; simp only [mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [hE]
    simp only [sum_empty, Nat.cast_zero, mul_zero, card_empty, zero_add]
    positivity

/-! ### Products of odd numbers -/

theorem padicValNat_two_mul_of_ne (hp2 : p ≠ 2) {x : ℕ} (hx : x ≠ 0) :
    padicValNat p (2 * x) = padicValNat p x := by
  rw [padicValNat.mul (by norm_num) hx]
  have : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)
  simp [padicValNat.eq_zero_of_not_dvd this]

theorem oddSum_add (hp2 : p ≠ 2) (A : ℕ) :
    (∑ j ∈ range A, padicValNat p (2 * j + 1)) + padicValNat p A.factorial
      = padicValNat p (2 * A).factorial := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [sum_range_succ, Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero A)]
    have h2 : 2 * (A + 1) = (2 * A + 1) + 1 := by ring
    rw [h2, Nat.factorial_succ, Nat.factorial_succ,
      padicValNat.mul (by omega) (by positivity), padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    have h3 : 2 * A + 1 + 1 = 2 * (A + 1) := by ring
    rw [h3, padicValNat_two_mul_of_ne hp2 (by omega)]
    omega

/-- `(p-1) Σ_{j<A} v_p(2j+1) ≥ A - (p-1)(Λ(2A)+1)` for odd `p`. -/
theorem sub_one_mul_oddSum_ge (hp2 : p ≠ 2) (A : ℕ) :
    (A : ℤ) - ((p - 1 : ℕ) : ℤ) * ((Nat.log p (2 * A) : ℤ) + 1)
      ≤ ((p - 1 : ℕ) : ℤ) * ((∑ j ∈ range A, padicValNat p (2 * j + 1) : ℕ) : ℤ) := by
  have h := oddSum_add (p := p) hp2 A
  have hu := legendre_upper (p := p) A
  have hl := legendre_lower (p := p) (2 * A)
  have h' : ((∑ j ∈ range A, padicValNat p (2 * j + 1) : ℕ) : ℤ)
      = (padicValNat p (2 * A).factorial : ℤ) - (padicValNat p A.factorial : ℤ) := by
    rw [← h]; push_cast; ring
  rw [h', mul_sub]
  have hc : ((2 * A : ℕ) : ℤ) = 2 * (A : ℤ) := by push_cast; ring
  rw [hc] at hl
  linarith

end ZetaIrr.Arith
