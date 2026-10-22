/-
# Lemma 4 for instance Z7: the fields `D`, `D_pos`, `int_ρ`, `int_τ` of `Z7.Hyp`, and the
# decomposition of `log D_n - G log n!` by prime ranges

* `D_pos_Z7`, `int_rho_Z7`, `int_tau_Z7`: exactly the forms of the `Z7.Hyp` fields
  (`ZetaIrrational/FamilyZ7.lean`) with `ρ = (pf m).rho`, `τ m j = (pf m).tau (2j-3)`, and
  `D = ZetaIrr.Z7.Arith.D`.
* `log_D_sub_eq`: `log D_n - G log n! = Σ_{p ≤ n} (E_p - G v_p(n!)) log p`.
* `log_D_sub_le`: the explicit split
  `log D_n - G log n! ≤ 182 ⌊√𝒩⌋ log 𝒩 + Σ_{p prime, p ≤ n, 𝒩 < p²} (Esharp_p - G ⌊n/p⌋) log p`,
  where the last sum is the one integrated by the A-certificate (Lemma 5). The primes `p > n`
  contribute nothing (`E_p = 0`), and there is no exceptional prime.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Arith.Size

set_option linter.unusedSectionVars false

namespace ZetaIrr.Z7.Arith

open Finset ZetaIrr.Arith

/-! ### Positivity and integrality -/

theorem D_pos_Z7 : ∀ m, 0 < D m := D_pos

theorem int_rho_Z7 : ∀ m, ∃ z : ℤ, (z : ℚ) = D m * (pf m).rho := int_rho

theorem int_tau_Z7 : ∀ m j, ∃ z : ℤ, (z : ℚ) = D m * (pf m).tau (2 * j - 3) :=
  fun m j => int_tau m (2 * j - 3)

/-! ### `log D_n - G log n!` as a sum over primes -/

theorem log_D_eq (m : ℕ) :
    Real.log ((D m : ℚ) : ℝ) = ∑ p ∈ primesD m, (Ep m p : ℝ) * Real.log p := by
  unfold D
  rw [Rat.cast_prod, Real.log_prod (fun p hp => by
    have := (mem_filter.mp hp).2.pos
    push_cast; exact zpow_ne_zero _ (by exact_mod_cast this.ne'))]
  refine sum_congr rfl (fun p _ => ?_)
  push_cast
  rw [Real.log_zpow]

theorem padicValNat_factorial_of_lt {p n : ℕ} (hp : p.Prime) (h : n < p) :
    padicValNat p n.factorial = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun hd => absurd ((Nat.Prime.dvd_factorial hp).mp hd) (by omega))

theorem log_factorial_eq (m : ℕ) :
    Real.log ((nOf m).factorial : ℝ)
      = ∑ p ∈ primesD m, (padicValNat p (nOf m).factorial : ℝ) * Real.log p := by
  set N := (nOf m).factorial
  have hN : N ≠ 0 := Nat.factorial_ne_zero _
  have h1 := Nat.prod_pow_prime_padicValNat N hN (N + nOf m + 1) (by omega)
  have h2 : ∏ p ∈ primesD m, p ^ padicValNat p N
      = ∏ p ∈ (range (N + nOf m + 1)).filter Nat.Prime, p ^ padicValNat p N := by
    refine prod_subset (fun p hp => ?_) (fun p hp hnot => ?_)
    · simp only [primesD, mem_filter, mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩
    · simp only [primesD, mem_filter, mem_range, not_and] at hp hnot
      have hlt : nOf m < p := by
        by_contra hc; exact hnot (by omega) hp.2
      rw [padicValNat_factorial_of_lt hp.2 hlt, pow_zero]
  rw [h1] at h2
  have h3 : (N : ℝ) = ((∏ p ∈ primesD m, p ^ padicValNat p N : ℕ) : ℝ) := by rw [h2]
  push_cast at h3
  rw [h3, Real.log_prod (fun p hp => by
    have := (mem_filter.mp hp).2.pos
    exact pow_ne_zero _ (by exact_mod_cast this.ne'))]
  refine sum_congr rfl (fun p _ => ?_)
  rw [Real.log_pow]

theorem log_D_sub_eq (m : ℕ) :
    Real.log ((D m : ℚ) : ℝ) - (G : ℝ) * Real.log ((nOf m).factorial : ℝ)
      = ∑ p ∈ primesD m,
          ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ)) * Real.log p := by
  rw [log_D_eq, log_factorial_eq, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl (fun p _ => ?_)
  ring

/-- For `n < p²`, `v_p(n!) = ⌊n/p⌋`. -/
theorem padicValNat_factorial_of_sq {p n : ℕ} (hp : p.Prime) (h : n < p ^ 2) :
    padicValNat p n.factorial = n / p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [padicValNat_factorial (b := 2)]
  · simp
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · exact Nat.log_lt_of_lt_pow (by omega) h

/-- The sharp prime range `√𝒩 < p ≤ n`. -/
def sharpPrimes (m : ℕ) : Finset ℕ := (primesD m).filter (fun p => NN m < p ^ 2)

/-- **The split of `log D_n - G log n!`.** The sharp range `√𝒩 < p ≤ n` is left as the sum that
Lemma 5 (the A-certificate) bounds; the small primes are bounded explicitly. -/
theorem log_D_sub_le (m : ℕ) :
    Real.log ((D m : ℚ) : ℝ) - (G : ℝ) * Real.log ((nOf m).factorial : ℝ)
      ≤ 182 * (Nat.sqrt (NN m) : ℝ) * Real.log (NN m)
        + ∑ p ∈ sharpPrimes m,
            ((Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ)) * Real.log p := by
  rw [log_D_sub_eq]
  set f : ℕ → ℝ := fun p =>
    ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ)) * Real.log p with hf
  rw [← sum_filter_add_sum_filter_not (primesD m) (fun p => p ^ 2 ≤ NN m)]
  have hsmall : ∑ p ∈ (primesD m).filter (fun p => p ^ 2 ≤ NN m), f p
      ≤ 182 * (Nat.sqrt (NN m) : ℝ) * Real.log (NN m) := by
    refine le_trans (le_of_eq ?_) (small_primes_sum_le m)
    refine sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [primesD, mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨⟨_, hpP⟩, hpN⟩
      exact ⟨⟨hpP.two_le, Nat.le_sqrt'.mpr hpN⟩, hpP⟩
    · rintro ⟨⟨_, hpS⟩, hpP⟩
      have hpN := Nat.le_sqrt'.mp hpS
      refine ⟨⟨?_, hpP⟩, hpN⟩
      unfold NN at hpN; unfold nOf
      by_contra hc
      nlinarith
  have hlarge : ∑ p ∈ (primesD m).filter (fun p => ¬ p ^ 2 ≤ NN m), f p
      = ∑ p ∈ sharpPrimes m,
          ((Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ)) * Real.log p := by
    refine sum_congr ?_ (fun p hp => ?_)
    · ext p
      simp only [sharpPrimes, mem_filter, not_le]
    · simp only [sharpPrimes, primesD, mem_filter, mem_range] at hp
      have hpn : ¬ nOf m < p := by omega
      have hEp : Ep m p = Esharp m p := by simp [Ep, hpn, hp.2]
      have hv : padicValNat p (nOf m).factorial = nOf m / p :=
        padicValNat_factorial_of_sq hp.1.2 (lt_trans (nOf_lt_NN m) hp.2)
      simp only [hf, hEp, hv]
  rw [hlarge]
  linarith

end ZetaIrr.Z7.Arith
