/-
# Lemma B and the assembly of ρ, τ (PROOF_ZETA §3–§4), for general `PFData`

* elementary valuation facts: `padicValRat_int_le` (`|z| < p^{e+1}` gives `v_p(z) ≤ e`),
  `padicValRat_int_le_ind`, `vge_ind_int`, `padicValRat_int_eq_zero`;
* `vge_Hq` (**Lemma B**): if `v_p(m) ≤ λ` for every `1 ≤ m ≤ k`, then `v_p(H_k^{(j)}) ≥ -jλ`;
  `vge_Hq_of_lt`: `H_k^{(j)}` is `p`-integral for `k < p`;
* `vge_tau`, `vge_rho`: termwise bounds for `τ_i = (i)_4 Σ_k a_{i,k}` and
  `ρ = -Σ a_{i,k} (i)_4 H_k^{(i+4)}`;
* Legendre-type sums over intervals: `sub_one_mul_sum_Icc_ge` (lower bound) and `pole_sum_le`
  (upper bound for `Σ_{k' ∈ [a,b], k' ≠ k} v_p(k' - k)`).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Arith.Valuation
import ZetaIrrational.Arith.Legendre
import ZetaIrrational.Expansion

set_option linter.unusedSectionVars false

namespace ZetaIrr.Arith

open Finset ZetaIrr
open ZetaIrr.PFData (Hq)

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Elementary facts -/

theorem padicValNat_le_of_lt {z e : ℕ} (hz : 0 < z) (h : z < p ^ (e + 1)) :
    padicValNat p z ≤ e := by
  by_contra hc
  have h1 : p ^ (e + 1) ∣ z :=
    (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
  exact absurd (Nat.le_of_dvd hz h1) (not_le.mpr h)

theorem padicValRat_int_le {z : ℤ} (hz : z ≠ 0) {e : ℕ} (h : z.natAbs < p ^ (e + 1)) :
    padicValRat p (z : ℚ) ≤ e := by
  rw [padicValRat.of_int]
  exact_mod_cast padicValNat_le_of_lt (Int.natAbs_pos.mpr hz) h

theorem padicValRat_int_eq_zero {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : padicValRat p (z : ℚ) = 0 := by
  simp [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd h]

theorem padicValRat_int_le_ind {z : ℤ} (hz : z ≠ 0) (h : z.natAbs < p ^ 2) :
    padicValRat p (z : ℚ) ≤ if (p : ℤ) ∣ z then 1 else 0 := by
  split_ifs with hd
  · exact_mod_cast padicValRat_int_le hz (e := 1) h
  · rw [padicValRat_int_eq_zero hd]

theorem vge_ind_int (z : ℤ) : vge p (if (p : ℤ) ∣ z then 1 else 0) (z : ℚ) := by
  split_ifs with hd
  · exact vge_int_dvd hd
  · exact vge_int z

theorem padicValRat_prod {ι : Type*} (T : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ T, f i ≠ 0) :
    padicValRat p (∏ i ∈ T, f i) = ∑ i ∈ T, padicValRat p (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValRat.mul (hf a (mem_insert_self a T))
      (prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-! ### Lemma B -/

/-- **Lemma B.** If `v_p(m'+1) ≤ λ` for every `m' < k`, then `v_p(H_k^{(j)}) ≥ -jλ`. -/
theorem vge_Hq (j k : ℕ) (lam : ℤ)
    (h : ∀ m' < k, padicValRat p ((m' : ℚ) + 1) ≤ lam) : vge p (-(j * lam)) (Hq j k) := by
  unfold Hq
  refine vge_sum _ _ (fun m' hm' => ?_)
  have hm : m' < k := mem_range.mp hm'
  rw [one_div, ← inv_pow]
  simpa using vge_pow (vge_inv (h m' hm)) j

/-- The bound `v_p(m'+1) ≤ e` for `m' + 1 < p^{e+1}`. -/
theorem padicValRat_succ_le {m' e : ℕ} (h : m' + 1 < p ^ (e + 1)) :
    padicValRat p ((m' : ℚ) + 1) ≤ e := by
  have : ((m' : ℚ) + 1) = (((m' + 1 : ℕ) : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  exact padicValRat_int_le (by omega) (by rw [Int.natAbs_natCast]; exact h)

/-- **Lemma B, first bullet.** `H_k^{(j)}` is `p`-integral when `k < p`. -/
theorem vge_Hq_of_lt (j k : ℕ) (hk : k < p) : vge p 0 (Hq j k) := by
  have h := vge_Hq (p := p) j k 0 (fun m' hm' => by
    have := padicValRat_succ_le (p := p) (m' := m') (e := 0) (by rw [zero_add, pow_one]; omega)
    simpa using this)
  simpa using h

/-! ### Assembly of τ and ρ -/

lemma rise_four_eq (i : ℕ) : rise i 4 = ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) := by
  rw [rise_four]; push_cast; ring

/-- `τ_i` is bounded by bounds on the `a_{i,k}`. -/
theorem vge_tau (P : PFData) (i : ℕ) (E : ℤ)
    (h : ∀ k ≤ P.K, vge p E (P.a i k)) : vge p E (P.tau i) := by
  unfold PFData.tau
  refine vge_sum _ _ (fun k hk => ?_)
  have hk' : k ≤ P.K := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [rise_four_eq]
  simpa using vge_mul (h k hk') (vge_nat (p := p) (i * (i + 1) * (i + 2) * (i + 3)))

/-- `ρ` is bounded by bounds on `a_{i,k} H_k^{(i+4)}`. -/
theorem vge_rho (P : PFData) (E : ℤ)
    (h : ∀ k ≤ P.K, ∀ i ∈ Icc 1 P.I, vge p E (P.a i k * Hq (i + 4) k)) :
    vge p E P.rho := by
  unfold PFData.rho
  refine vge_neg (vge_sum _ _ (fun k hk => vge_sum _ _ (fun i hi => ?_)))
  have hk' : k ≤ P.K := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have h1 := vge_mul (h k hk' i hi) (vge_nat (p := p) (i * (i + 1) * (i + 2) * (i + 3)))
  rw [rise_four_eq]
  have he : P.a i k * ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) * Hq (i + 4) k
      = P.a i k * Hq (i + 4) k * ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) := by ring
  rw [he]
  simpa using h1

/-! ### Legendre-type sums over intervals -/

/-- `(p-1) Σ_{d=A}^{B} v_p(d) ≥ (B + 1 - A) - (p-1)(Λ(B)+1)` for `1 ≤ A ≤ B + 1`. -/
theorem sub_one_mul_sum_Icc_ge {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B + 1) :
    ((B : ℤ) + 1 - A) - ((p - 1 : ℕ) : ℤ) * ((Nat.log p B : ℤ) + 1)
      ≤ ((p - 1 : ℕ) : ℤ) * ((∑ d ∈ Icc A B, padicValNat p d : ℕ) : ℤ) := by
  have h := sum_Icc_padicValNat (p := p) hA hAB
  have hu := legendre_upper (p := p) (A - 1)
  have hl := legendre_lower (p := p) B
  have h' : ((∑ d ∈ Icc A B, padicValNat p d : ℕ) : ℤ)
      = (padicValNat p B.factorial : ℤ) - (padicValNat p (A - 1).factorial : ℤ) := by
    rw [← h]; push_cast; ring
  rw [h', mul_sub]
  have hc : ((A - 1 : ℕ) : ℤ) = (A : ℤ) - 1 := by omega
  rw [hc] at hu
  linarith

/-- `(p-1) Σ_{k' ∈ [a,b], k' ≠ k} v_p(k'-k) ≤ #[a,b] + 2(p-1)(⌊log_p N⌋+1)` for `a, k ≤ N`. -/
theorem pole_sum_le {a b k N : ℕ} (ha : a ≤ N) (hk : k ≤ N) :
    ((p - 1 : ℕ) : ℤ) * ∑ k' ∈ (Icc a b).erase k, (padicValInt p ((k' : ℤ) - k) : ℤ)
      ≤ ((#(Icc a b) : ℕ) : ℤ) + 2 * ((p - 1 : ℕ) : ℤ) * ((Nat.log p N : ℤ) + 1) := by
  rw [← sum_filter_add_sum_filter_not ((Icc a b).erase k) (fun k' => k < k')]
  have hU : ((Icc a b).erase k).filter (fun k' => k < k') = Icc (max a (k + 1)) b := by
    ext x; simp only [mem_filter, mem_erase, mem_Icc]; omega
  have hL : ((Icc a b).erase k).filter (fun k' => ¬ k < k') = Ico a (min (b + 1) k) := by
    ext x; simp only [mem_filter, mem_erase, mem_Icc, mem_Ico]; omega
  rw [hU, hL]
  have hU' : ∑ k' ∈ Icc (max a (k + 1)) b, (padicValInt p ((k' : ℤ) - k) : ℤ)
      = ((∑ d ∈ Icc (max a (k + 1) - k) (b - k), padicValNat p d : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_nbij' (fun k' => k' - k) (fun d => d + k) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx; omega
    · intro x hx
      simp only [mem_Icc] at hx
      congr 1; unfold padicValInt; congr 1; omega
  have hL' : ∑ k' ∈ Ico a (min (b + 1) k), (padicValInt p ((k' : ℤ) - k) : ℤ)
      = ((∑ d ∈ Icc (k - min (b + 1) k + 1) (k - a), padicValNat p d : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_nbij' (fun k' => k - k') (fun d => k - d) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Icc, mem_Ico, Finset.mem_coe] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc, mem_Ico, Finset.mem_coe] at hx ⊢; omega
    · intro x hx; simp only [mem_Ico, Finset.mem_coe] at hx; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx; omega
    · intro x hx
      simp only [mem_Ico] at hx
      congr 1; unfold padicValInt; congr 1; omega
  rw [hU', hL', mul_add]
  have h1 := sub_one_mul_sum_Icc_le' (p := p) (A := max a (k + 1) - k) (B := b - k) (N := N)
    (by omega) (by omega)
  have h2 := sub_one_mul_sum_Icc_le' (p := p) (A := k - min (b + 1) k + 1) (B := k - a) (N := N)
    (by omega) (by omega)
  have hc : ((#(Icc (max a (k + 1) - k) (b - k)) : ℕ) : ℤ)
      + ((#(Icc (k - min (b + 1) k + 1) (k - a)) : ℕ) : ℤ) ≤ ((#(Icc a b) : ℕ) : ℤ) := by
    simp only [Nat.card_Icc]; omega
  linarith

end ZetaIrr.Arith
