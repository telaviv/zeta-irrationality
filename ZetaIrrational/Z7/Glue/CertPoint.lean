/-
# Glue (Z7): Lemma 5 (a) for the exponent `Arith.Esharp`, from `CertA.pointwise_le_eStar_prime`

Here `Arith` is `ZetaIrr.Z7.Arith` and `CertA` is `ZetaIrr.Z7.CertA`.

The two files define `c_p(k)` and `P_{p,j}(k)` separately: `Arith.cp ≥ CertA.cp` (Arith also
counts the `e`-factor; `cp_le`) and `Arith.Ppj = CertA.Ppj` (`Ppj_eq`), so the per-`k` exponent
satisfies `Arith.eK ≤ CertA.epk` (`eK_le_epk`). With `eStarInt ≥ 0` (which covers the `max(0, ·)`
in the definition of `E_p`, Lemma 4) this gives `E_p - G⌊n/p⌋ ≤ e*(n/p)` for every prime `p ≤ n`
(`Esharp_sub_le_eStar`; the restriction `√𝒩 < p` is not needed here).
-/
import ZetaIrrational.Z7.CertA.Pointwise
import ZetaIrrational.Z7.Arith.Size

set_option maxRecDepth 8192

namespace ZetaIrr.Z7

open Finset

/-! ### Comparing the two sets of counts -/

lemma count_run1 (m p k : ℕ) :
    ∑ l ∈ Icc 1 (220 * (m + 1)), (if (p : ℤ) ∣ Arith.zv k (l : ℤ) then (1 : ℤ) else 0)
      = (#{l ∈ Icc (1 : ℤ) (220 * ((m : ℤ) + 1)) | (p : ℤ) ∣ (k : ℤ) + l} : ℕ) := by
  have h1 : ∑ l ∈ Icc 1 (220 * (m + 1)), (if (p : ℤ) ∣ Arith.zv k (l : ℤ) then (1 : ℤ) else 0)
      = ∑ z ∈ Icc (1 : ℤ) (220 * ((m : ℤ) + 1)), (if (p : ℤ) ∣ (k : ℤ) + z then (1 : ℤ) else 0) := by
    refine Finset.sum_nbij' (fun l => (l : ℤ)) (fun z => z.toNat) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx ⊢; omega
    · intro x _; simp
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx; omega
    · intro x _
      rw [Arith.zv, show -(k : ℤ) - (x : ℤ) = -((k : ℤ) + x) by ring]
      simp only [dvd_neg]
  rw [h1, sum_boole]

lemma count_run2 (m p k : ℕ) :
    ∑ l ∈ Icc (nOf m + 1) (460 * (m + 1)),
        (if (p : ℤ) ∣ Arith.zv k (-(l : ℤ)) then (1 : ℤ) else 0)
      = (#{l ∈ Icc ((nOf m : ℤ) + 1) (460 * ((m : ℤ) + 1)) | (p : ℤ) ∣ l - k} : ℕ) := by
  have h1 : ∑ l ∈ Icc (nOf m + 1) (460 * (m + 1)),
        (if (p : ℤ) ∣ Arith.zv k (-(l : ℤ)) then (1 : ℤ) else 0)
      = ∑ z ∈ Icc ((nOf m : ℤ) + 1) (460 * ((m : ℤ) + 1)),
          (if (p : ℤ) ∣ z - k then (1 : ℤ) else 0) := by
    refine Finset.sum_nbij' (fun l => (l : ℤ)) (fun z => z.toNat) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Icc, Finset.mem_coe, nOf] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe, nOf] at hx ⊢; omega
    · intro x _; simp
    · intro x hx; simp only [mem_Icc, Finset.mem_coe, nOf] at hx; omega
    · intro x _
      rw [Arith.zv, show -(k : ℤ) - -(x : ℤ) = (x : ℤ) - k by ring]
  rw [h1, sum_boole]

lemma cp_le (m p k : ℕ) : ((CertA.cp m p k : ℕ) : ℤ) ≤ Arith.cp m p k := by
  unfold CertA.cp Arith.cp
  rw [Arith.sum_Zs, ← mul_sum, ← mul_sum, count_run1, count_run2]
  have : (0 : ℤ) ≤ if (p : ℤ) ∣ (nOf m : ℤ) - 2 * k then 1 else 0 := by split_ifs <;> norm_num
  push_cast
  linarith

lemma Ppj_eq (m p k : ℕ) (b : ℕ × ℕ) : Arith.Ppj m p k b = CertA.Ppj m p b.1 k := by
  unfold Arith.Ppj CertA.Ppj blk
  refine Finset.card_bij (fun a _ => (a : ℤ)) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_erase, mem_Icc] at ha ⊢
    refine ⟨⟨by exact_mod_cast ha.1.1, by exact_mod_cast ha.1.2.1, by exact_mod_cast ha.1.2.2⟩,
      ha.2⟩
  · intro a _ b _ h; exact_mod_cast h
  · intro z hz
    simp only [mem_filter, mem_erase, mem_Icc] at hz
    refine ⟨z.toNat, ?_, by omega⟩
    simp only [mem_filter, mem_erase, mem_Icc]
    refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]; exact hz.2

lemma Ptot_eq_Pp (m p k : ℕ) : ((Arith.Ptot m p k : ℕ) : ℤ) = CertA.Pp m p k := by
  rw [Arith.Ptot_cast, CertA.Pp]
  exact congrArg List.sum (List.map_congr_left (fun b _ => by rw [Ppj_eq]))

/-- `Arith.eK ≤ CertA.epk` where `B_k ≥ 1`. -/
lemma eK_le_epk (m p k : ℕ) (hB : Bk m k ≠ 0) : Arith.eK m p k ≤ CertA.epk m p k := by
  have hcp := cp_le m p k
  have hP := Ptot_eq_Pp m p k
  unfold Arith.eK CertA.epk
  rw [if_neg hB]
  by_cases hpk : p ≤ k
  · rw [if_pos hpk, if_pos hpk]; linarith
  · rw [if_neg hpk, if_neg hpk]
    by_cases h0 : Arith.Ptot m p k = 0
    · rw [if_pos h0, if_neg (by rw [← hP, h0]; norm_num)]
    · rw [if_neg h0, if_pos (by rw [← hP]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0)]
      linarith

/-! ### (a) the pointwise bound for the exponent `Arith.Esharp` -/

/-- **Lemma 5 (a) for the exponent `Arith.Esharp`.** For primes `p ≤ n`:
`E_p - G⌊n/p⌋ ≤ e*(n/p)`. -/
theorem Esharp_sub_le_eStar (m p : ℕ) (hp : p.Prime) (hpn : p ≤ nOf m) :
    (Arith.Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ) ≤
      ((CertA.eStar ((nOf m : ℚ) / p) : ℚ) : ℝ) := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hx1 : 1 ≤ (nOf m : ℚ) / p := by
    rw [le_div_iff₀ hp', one_mul]; exact_mod_cast hpn
  have hfl : ⌊(nOf m : ℚ) / p⌋ = ((nOf m / p : ℕ) : ℤ) := by
    rw [Rat.floor_natCast_div_natCast]; push_cast; rfl
  -- the value `0`
  have h0 : -(G : ℚ) * ((nOf m / p : ℕ) : ℚ) ≤ CertA.eStar ((nOf m : ℚ) / p) := by
    rw [CertA.eStar, if_pos hx1, hfl]
    have := CertA.eStarInt_nonneg ((nOf m : ℚ) / p)
    have : (0 : ℚ) ≤ (CertA.eStarInt ((nOf m : ℚ) / p) : ℚ) := by exact_mod_cast this
    simp only [Int.cast_natCast]
    linarith
  -- each `eK`
  have hk : ∀ k ∈ range (nOf m + 1), (Arith.eK m p k : ℚ) - G * ((nOf m / p : ℕ) : ℚ)
      ≤ CertA.eStar ((nOf m : ℚ) / p) := by
    intro k _
    by_cases hB : Bk m k = 0
    · rw [Arith.eK, if_pos hB, Int.cast_zero]; linarith
    · have h1 := CertA.pointwise_le_eStar_prime m p k hp hpn (Nat.one_le_iff_ne_zero.mpr hB)
      rw [hfl] at h1
      have h2 : (Arith.eK m p k : ℚ) ≤ (CertA.epk m p k : ℚ) := by
        exact_mod_cast eK_le_epk m p k hB
      simp only [Int.cast_natCast] at h1
      linarith
  have hE : (Arith.Esharp m p : ℚ) - G * ((nOf m / p : ℕ) : ℚ)
      ≤ CertA.eStar ((nOf m : ℚ) / p) := by
    unfold Arith.Esharp
    rcases le_total 0 ((range (nOf m + 1)).sup' nonempty_range_add_one (Arith.eK m p)) with h | h
    · rw [max_eq_right h]
      obtain ⟨k, hkm, hkeq⟩ := exists_mem_eq_sup' nonempty_range_add_one (Arith.eK m p)
      rw [hkeq]
      exact hk k hkm
    · rw [max_eq_left h, Int.cast_zero]
      linarith
  exact_mod_cast hE

end ZetaIrr.Z7
