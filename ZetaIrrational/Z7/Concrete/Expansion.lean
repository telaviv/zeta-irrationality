/-
# Instance Z7: the partial-fraction expansion of `R_n` (discharges `Hyp.expansion`)

PROOF_ZETA §1–§3 for the concrete `Z7.R m` of `FamilyZ7.lean`, with the coefficients `Z7.a` of
`Z7/Concrete/Data.lean` (Taylor coefficients of `f_k(t₀ + ε)`, `t₀ = -k`).

* `Zs`, `prod_Zs`: the zero set `[1, rn] ∪ [-(1+r)n, -n-1]` (multiplicity 5) as one `Finset ℤ`;
* `R_eq_pfR`: `R m t = (pf m).R t` off the poles (partial-fraction identity, PROOF_ZETA §3);
* `pf_symmetric`, `pf_supported`: the data is mirror-symmetric (Lemma 2, `t ↦ -n-t`, `deg R` odd)
  and supported in `i ≤ 18`;
* `pf_tau_one`: `τ₁ = 0` (Lemma 3: `deg R ≤ -2`, via `PF.pf_top_coeff`);
* `iteratedDeriv_R`: `R⁽ʲ⁾ = (pf m).Rd j` on `t > 0`;
* `expansion_Z7`: `L m = ρ + Σ_{j=3}^{10} τ_{2j-3} ζ(2j+1)` (Lemma 3 for `R_n`; the `expansion`
  field of `Z7.Hyp`).

Method: `R m = N/D` for explicit polynomials over `ℚ` (`Npoly`, `Dpoly`), then the general
theory of `Concrete/PartialFrac.lean`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Concrete.PartialFracTop
import ZetaIrrational.Z7.Concrete.Blocks

set_option maxRecDepth 8192

namespace ZetaIrr.Z7

open Polynomial Finset Filter Topology
open scoped BigOperators

/-! ### The zero set -/

/-- The zeros `[1, rn] ∪ [-(1+r)n, -n-1]` (each of multiplicity 5), `rn = 220(m+1)`. -/
def Zs (m : ℕ) : Finset ℤ :=
  (Icc 1 (220 * (m + 1))).image (fun l : ℕ => (l : ℤ)) ∪
    (Icc (nOf m + 1) (460 * (m + 1))).image (fun l : ℕ => -(l : ℤ))

lemma mem_Zs (m : ℕ) (z : ℤ) : z ∈ Zs m ↔
    (1 ≤ z ∧ z ≤ 220 * ((m : ℤ) + 1)) ∨ (-(460 * ((m : ℤ) + 1)) ≤ z ∧ z ≤ -(240 * ((m : ℤ) + 1)) - 1) := by
  simp only [Zs, mem_union, mem_image, mem_Icc, nOf]
  constructor
  · rintro (⟨l, ⟨h1, h2⟩, rfl⟩ | ⟨l, ⟨h1, h2⟩, rfl⟩)
    · left; omega
    · right; omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left; exact ⟨z.toNat, ⟨by omega, by omega⟩, by omega⟩
    · right; exact ⟨(-z).toNat, ⟨by omega, by omega⟩, by omega⟩

lemma Zs_disjoint (m : ℕ) : Disjoint ((Icc 1 (220 * (m + 1))).image (fun l : ℕ => (l : ℤ)))
    ((Icc (nOf m + 1) (460 * (m + 1))).image (fun l : ℕ => -(l : ℤ))) := by
  rw [disjoint_left]
  intro z h1 h2
  simp only [mem_image, mem_Icc] at h1 h2
  obtain ⟨a, _, rfl⟩ := h1
  obtain ⟨b, _, hb⟩ := h2
  omega

/-- Splitting a product over the zero set into the two runs. -/
lemma prod_Zs {M : Type*} [CommMonoid M] (m : ℕ) (f : ℤ → M) :
    ∏ z ∈ Zs m, f z = (∏ l ∈ Icc 1 (220 * (m + 1)), f l) *
      ∏ l ∈ Icc (nOf m + 1) (460 * (m + 1)), f (-(l : ℤ)) := by
  rw [Zs, prod_union (Zs_disjoint m), prod_image (fun a _ b _ h => by exact_mod_cast h),
    prod_image (fun a _ b _ h => by simpa using h)]

lemma card_Zs (m : ℕ) : (Zs m).card = 440 * (m + 1) := by
  rw [Zs, card_union_of_disjoint (Zs_disjoint m),
    card_image_of_injective _ (fun a b h => by exact_mod_cast h),
    card_image_of_injective _ (fun a b h => by simpa using h), Nat.card_Icc, Nat.card_Icc, nOf]
  omega

/-! ### `R = N/D` -/

/-- The numerator `(2t + n) Π_z (t - z)^5`. -/
noncomputable def Npoly (m : ℕ) : ℚ[X] :=
  (C 2 * X + C (nOf m : ℚ)) * ∏ z ∈ Zs m, (X - C (z : ℚ)) ^ 5

/-- The pole centres `-k`. -/
def cen (k : ℕ) : ℚ := -(k : ℚ)

/-- The denominator `Π_{k ≤ n} (t + k)^{B_k}`. -/
noncomputable def Dpoly (m : ℕ) : ℚ[X] := PF.den (range (nOf m + 1)) cen (Bk m)

lemma cen_injOn (s : Set ℕ) : Set.InjOn cen s := fun a _ b _ h => by
  simp only [cen, neg_inj, Nat.cast_inj] at h
  exact h

lemma natDegree_Npoly_le (m : ℕ) : (Npoly m).natDegree ≤ 1 + 5 * (440 * (m + 1)) := by
  unfold Npoly
  refine (natDegree_mul_le).trans (add_le_add natDegree_linear_le ?_)
  refine (natDegree_prod_le _ _).trans ?_
  rw [← card_Zs, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun l _ => natDegree_pow_le.trans ?_)
  rw [natDegree_X_sub_C]

/-- `deg N + 1 < deg D`, i.e. `deg R_n ≤ -2`. -/
lemma natDegree_Npoly_lt (m : ℕ) :
    (Npoly m).natDegree + 1 < ∑ k ∈ range (nOf m + 1), Bk m k := by
  rw [sum_Bk]
  have := natDegree_Npoly_le m
  omega

lemma aeval_Dpoly (m : ℕ) (t : ℝ) :
    aeval t (Dpoly m) = (blocks.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)), (t + (k : ℝ))) ^ b.2)).prod := by
  change _ = (blocks.map (fun b => (∏ k ∈ blk m b, (t + (k : ℝ))) ^ b.2)).prod
  rw [prod_blocks, Dpoly, PF.den, map_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  simp only [map_pow, map_sub, aeval_X, aeval_C, eq_ratCast, cen]
  push_cast
  ring

lemma aeval_Npoly (m : ℕ) (t : ℝ) :
    aeval t (Npoly m) = (2 * t + (nOf m : ℝ)) *
      (∏ l ∈ Icc 1 (220 * (m + 1)), (t - (l : ℝ)) ^ 5) *
      (∏ l ∈ Icc (nOf m + 1) (460 * (m + 1)), (t + (l : ℝ)) ^ 5) := by
  have h : aeval t (Npoly m) = (2 * t + (nOf m : ℝ)) * ∏ z ∈ Zs m, (t - (z : ℝ)) ^ 5 := by
    simp only [Npoly, map_mul, map_add, map_prod, map_pow, map_sub, aeval_X, aeval_C, eq_ratCast]
    push_cast
    ring
  rw [h, prod_Zs]
  simp only [Int.cast_natCast, Int.cast_neg, sub_neg_eq_add]
  ring

/-- `R m = N / D` everywhere (both sides are `0` at the poles). -/
lemma R_eq_ratfun (m : ℕ) (t : ℝ) : R m t = aeval t (Npoly m) / aeval t (Dpoly m) := by
  rw [R, aeval_Npoly, aeval_Dpoly]

/-! ### The power series side -/

lemma shiftPS_cof (m k : ℕ) :
    PF.shiftPS (cen k) (PF.cof (range (nOf m + 1)) cen (Bk m) k)
      = ∏ k' ∈ (range (nOf m + 1)).erase k,
          (PowerSeries.C ((k' : ℚ) - k) + PowerSeries.X) ^ Bk m k' := by
  unfold PF.cof
  rw [map_prod]
  refine Finset.prod_congr rfl (fun k' _ => ?_)
  rw [map_pow, PF.shiftPS_X_sub_C]
  congr 3
  simp only [cen]
  ring

lemma denSeries_eq (m k : ℕ) :
    denSeries m k = ∏ k' ∈ (range (nOf m + 1)).erase k,
      (PowerSeries.C ((k' : ℚ) - k) + PowerSeries.X)⁻¹ ^ Bk m k' := by
  change (blocks.map (fun b =>
    (∏ k' ∈ (blk m b).erase k, (PowerSeries.C ((k' : ℚ) - k) + PowerSeries.X)⁻¹) ^ b.2)).prod = _
  rw [prod_list_blocks _ (fun b => (blk m b).erase k) ((range (nOf m + 1)).erase k) blocks
    (fun b hb => Finset.erase_subset_erase k (blk_subset m b hb))]
  refine Finset.prod_congr rfl (fun k' hk' => ?_)
  have hne : k' ≠ k := Finset.ne_of_mem_erase hk'
  rw [Bk_eq]
  congr 2
  refine List.map_congr_left (fun b _ => ?_)
  simp [Finset.mem_erase, hne]

lemma denSeries_mul (m k : ℕ) :
    denSeries m k * PF.shiftPS (cen k) (PF.cof (range (nOf m + 1)) cen (Bk m) k) = 1 := by
  rw [denSeries_eq, shiftPS_cof, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun k' hk' => ?_)
  have hne : k' ≠ k := Finset.ne_of_mem_erase hk'
  rw [← mul_pow, PowerSeries.inv_mul_cancel, one_pow]
  simp only [map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero]
  rw [sub_ne_zero]
  exact_mod_cast hne

lemma numSeries_eq (m k : ℕ) : numSeries m k = PF.shiftPS (cen k) (Npoly m) := by
  unfold numSeries Npoly
  rw [map_mul, map_prod, prod_Zs, ← mul_assoc]
  have h1 : (PowerSeries.C ((nOf m : ℚ) - 2 * k) + 2 * PowerSeries.X : PowerSeries ℚ)
      = PF.shiftPS (cen k) (C 2 * X + C (nOf m : ℚ)) := by
    rw [map_add, map_mul, PF.shiftPS_C, PF.shiftPS_X, PF.shiftPS_C,
      show (nOf m : ℚ) - 2 * k = 2 * cen k + (nOf m : ℚ) by simp only [cen]; ring,
      map_add, map_mul, map_ofNat]
    ring
  have h2 : ∏ l ∈ Icc 1 (220 * (m + 1)), (PowerSeries.C (-(k : ℚ) - l) + PowerSeries.X) ^ 5
      = ∏ l ∈ Icc 1 (220 * (m + 1)), PF.shiftPS (cen k) ((X - C (((l : ℤ) : ℚ))) ^ 5) := by
    refine prod_congr rfl (fun l _ => ?_)
    rw [map_pow, PF.shiftPS_X_sub_C]
    congr 3
    all_goals (simp only [cen]; push_cast; ring)
  have h3 : ∏ l ∈ Icc (nOf m + 1) (460 * (m + 1)), (PowerSeries.C ((l : ℚ) - k) + PowerSeries.X) ^ 5
      = ∏ l ∈ Icc (nOf m + 1) (460 * (m + 1)),
          PF.shiftPS (cen k) ((X - C (((-(l : ℤ) : ℤ) : ℚ))) ^ 5) := by
    refine prod_congr rfl (fun l _ => ?_)
    rw [map_pow, PF.shiftPS_X_sub_C]
    congr 3
    all_goals (simp only [cen]; push_cast; ring)
  rw [h1, h2, h3]

lemma fSeries_eq (m k : ℕ) : fSeries m k = PF.shiftPS (cen k) (Npoly m) * denSeries m k := by
  rw [fSeries, numSeries_eq]

/-! ### 1. The partial-fraction identity -/

lemma nonpole_iff (m : ℕ) (t : ℝ) :
    (∀ k ∈ range (nOf m + 1), t ≠ ((cen k : ℚ) : ℝ)) ↔ ∀ k ≤ nOf m, t ≠ -(k : ℝ) := by
  have h : ∀ k : ℕ, ((cen k : ℚ) : ℝ) = -(k : ℝ) := fun k => by
    simp only [cen]; push_cast; ring
  simp only [Finset.mem_range, Nat.lt_succ_iff, h]

/-- **Partial-fraction identity** (PROOF_ZETA §3): off the poles, `R_n` equals the partial-fraction
sum with the Taylor-coefficient data `Z7.a`. -/
theorem R_eq_pfR (m : ℕ) (t : ℝ) (ht : ∀ k ≤ nOf m, t ≠ -(k : ℝ)) :
    R m t = (pf m).R t := by
  rw [R_eq_ratfun, Dpoly, PF.pf_eval' (range (nOf m + 1)) cen (Bk m) (Npoly m) (cen_injOn _)
    (by have := natDegree_Npoly_lt m; omega) (denSeries m) (fun k _ => denSeries_mul m k) t
    ((nonpole_iff m t).mpr ht)]
  rw [PFData.R_eq]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  change _ = ∑ i ∈ Icc 1 18, (a m i k : ℝ) * ((t + (k : ℝ)) ^ i)⁻¹
  have hshift : t - ((cen k : ℚ) : ℝ) = t + (k : ℝ) := by
    simp only [cen]; push_cast; ring
  rw [hshift]
  symm
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (Bk_le m k))]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Icc] at hi
    rw [a, if_pos hi, fSeries_eq]
  · intro i _ hi
    rw [Finset.mem_Icc, not_and_or] at hi
    rw [a, if_neg (by omega), Rat.cast_zero, zero_mul]

/-! ### 2. Support, mirror symmetry, `τ₁ = 0` -/

theorem pf_supported (m : ℕ) : (pf m).Supported := by
  intro i k hi
  change 18 < i at hi
  change a m i k = 0
  have := Bk_le m k
  rw [a, if_neg (by omega)]

lemma Npoly_mirror (m : ℕ) :
    (Npoly m).comp (C (-(nOf m : ℚ)) - X) = C (-1) * Npoly m := by
  set α : ℚ := -(nOf m : ℚ) with hα
  unfold Npoly
  rw [mul_comp]
  have h1 : (C 2 * X + C (nOf m : ℚ)).comp (C α - X)
      = C (-1) * (C 2 * X + C (nOf m : ℚ)) := by
    rw [add_comp, mul_comp, C_comp, C_comp, X_comp, hα]
    simp only [map_neg, map_one, show (C 2 : ℚ[X]) = 2 from map_ofNat C 2]
    ring
  have h2 : (∏ z ∈ Zs m, (X - C (z : ℚ)) ^ 5).comp (C α - X)
      = ∏ z ∈ Zs m, (X - C (z : ℚ)) ^ 5 := by
    change Polynomial.compRingHom (C α - X) _ = _
    rw [map_prod]
    have hfac : ∀ z : ℤ, Polynomial.compRingHom (C α - X) ((X - C (z : ℚ)) ^ 5)
        = -(X - C (((-(nOf m : ℤ) - z : ℤ)) : ℚ)) ^ 5 := by
      intro z
      rw [map_pow]
      change ((X - C (z : ℚ)).comp (C α - X)) ^ 5 = _
      rw [sub_comp, X_comp, C_comp, ← Odd.neg_pow (by decide)]
      congr 1
      rw [hα]
      push_cast
      simp only [map_sub, map_neg, map_natCast]
      ring
    simp only [hfac]
    rw [Finset.prod_neg, card_Zs,
      (show Even (440 * (m + 1)) from ⟨220 * (m + 1), by ring⟩).neg_one_pow, one_mul]
    refine Finset.prod_nbij' (fun z => -(nOf m : ℤ) - z) (fun z => -(nOf m : ℤ) - z)
      ?_ ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_coe, mem_Zs, nOf] at hz ⊢
      push_cast at hz ⊢
      omega
    · intro z hz
      simp only [Finset.mem_coe, mem_Zs, nOf] at hz ⊢
      push_cast at hz ⊢
      omega
    · intro z _
      ring
    · intro z _
      ring
    · intro z _
      rfl
  rw [h1, h2]
  ring

/-- **Lemma 2 data for Z7**: `a i (n-k) = (-1)^(i+1) a i k`. -/
theorem pf_symmetric (m : ℕ) : (pf m).Symmetric := by
  intro i k hk
  change k ≤ nOf m at hk
  change a m i (nOf m - k) = (-1) ^ (i + 1) * a m i k
  unfold a
  rw [Bk_mirror m k hk]
  split_ifs with h
  swap
  · simp
  rw [fSeries_eq, fSeries_eq]
  have hks : k ∈ range (nOf m + 1) := Finset.mem_range.mpr (by omega)
  have hsym := PF.pf_symm (range (nOf m + 1)) cen (Bk m) (Npoly m) (fun k => nOf m - k)
    (-(nOf m : ℚ)) (-1)
    (fun k hk => by
      simp only [Finset.mem_range] at hk ⊢
      omega)
    (fun k hk => by
      simp only [Finset.mem_range] at hk
      omega)
    (fun k hk => by
      simp only [Finset.mem_range] at hk
      simp only [cen]
      rw [Nat.cast_sub (by omega)]
      ring)
    (fun k hk => by
      simp only [Finset.mem_range] at hk
      exact Bk_mirror m k (by omega))
    (Npoly_mirror m) (by norm_num) (denSeries m) (fun k _ => denSeries_mul m k) k hks
    (Bk m k - i)
  rw [hsym]
  congr 1
  have hsum := Finset.sum_erase_add (range (nOf m + 1)) (Bk m) hks
  rw [sum_Bk] at hsum
  set E := ∑ k' ∈ (range (nOf m + 1)).erase k, Bk m k'
  rw [show ((-1 : ℚ) * (-1) ^ E * (-1) ^ (Bk m k - i)) = (-1) ^ (1 + E + (Bk m k - i)) by
    rw [pow_add, pow_add, pow_one]]
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := i + 1)]
  have hpar : (1 + E + (Bk m k - i)) % 2 = (i + 1) % 2 := by omega
  rw [hpar]

/-- **Lemma 3 (`τ₁ = 0`)**: the residues `a_{1,k}` sum to zero, since `deg R_n ≤ -2`. -/
theorem pf_tau_one (m : ℕ) : (pf m).tau 1 = 0 := by
  have h := PF.pf_top_coeff (range (nOf m + 1)) cen (Bk m) (Npoly m) (cen_injOn _)
    (natDegree_Npoly_lt m) (denSeries m) (fun k _ => denSeries_mul m k)
  unfold PFData.tau
  rw [← Finset.sum_mul]
  simp only [show (pf m).K = nOf m from rfl, show (pf m).a = a m from rfl]
  have : ∑ k ∈ range (nOf m + 1), a m 1 k = ∑ k ∈ range (nOf m + 1),
      (if 1 ≤ Bk m k then PowerSeries.coeff (Bk m k - 1)
        (PF.shiftPS (cen k) (Npoly m) * denSeries m k) else 0) := by
    refine sum_congr rfl (fun k _ => ?_)
    simp only [a, fSeries_eq, le_refl, true_and]
  rw [this, h, zero_mul]

/-! ### 3. Derivatives and the expansion -/

/-- `R_n⁽ʲ⁾ = (pf m).Rd j` on `t > 0` (there are no poles in `t > -3(m+1)`). -/
theorem iteratedDeriv_R (m : ℕ) {x : ℝ} (hx : 0 < x) (j : ℕ) :
    iteratedDeriv j (R m) x = (pf m).Rd j x :=
  (pf m).iteratedDeriv_eq_Rd isOpen_Ioi (fun _ ht => ht)
    (fun t ht => R_eq_pfR m t (fun k _ h => by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have ht' : (0 : ℝ) < t := ht
      linarith)) j hx

/-- **Lemma 3 for Z7** (the `expansion` field of `Z7.Hyp`, with `ρ = (pf m).rho` and
`τ m j = (pf m).tau (2j-3)`): `L_n = ρ + Σ_{j=3}^{10} τ_{2j-3} ζ(2j+1)`, so `ζ(3)`, `ζ(5)` and the
even zeta values do not occur. -/
theorem expansion_Z7 (m : ℕ) :
    L m = ((pf m).rho : ℝ)
      + ∑ j ∈ Icc 3 10, ((pf m).tau (2 * j - 3) : ℝ) * zetaR (2 * j + 1) := by
  rw [L, tsum_congr (fun t : ℕ => iteratedDeriv_R m (x := (t : ℝ) + 1) (by positivity) 4)]
  exact (pf m).tsum_R4_odd (pf_symmetric m) (pf_supported m) (pf_tau_one m) 10
    (show 18 + 2 ≤ 2 * 10 by norm_num)

end ZetaIrr.Z7
