/-
# The top coefficient of a partial-fraction decomposition (for PROOF_ZETA Lemma 3)

In the setting of `Concrete/PartialFrac.lean` (`N/D = Σ_k Σ_{j<B_k} [X^j]f_k (t-c_k)^j/(t-c_k)^{B_k}`),
the coefficient of `(t - c_k)^{-1}` is `[X^{B_k - 1}] f_k`, and the sum of these residues is the
coefficient of `X^{deg D - 1}` in `N`. So if `deg N + 1 < deg D` (i.e. `deg(N/D) ≤ -2`) the residues
sum to zero (`pf_top_coeff`). This is the `τ₁ = 0` of PROOF_ZETA Lemma 3.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Concrete.PartialFrac

namespace ZetaIrr.PF

open Polynomial Finset

variable {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℚ) (B : ι → ℕ)

lemma monic_cof (k : ι) : (cof s c B k).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => (monic_X_sub_C _).pow _)

lemma natDegree_cof (k : ι) : (cof s c B k).natDegree = ∑ k' ∈ s.erase k, B k' := by
  unfold cof
  rw [natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_sub_C _).pow _)]
  simp

omit [DecidableEq ι] in
lemma coeff_X_sub_C_pow_self (a : ℚ) (j : ℕ) : ((X - C a) ^ j).coeff j = 1 := by
  have h := (monic_X_sub_C a).pow j
  have hd : ((X - C a) ^ j).natDegree = j := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have := h.coeff_natDegree
  rwa [hd] at this

omit [DecidableEq ι] in
lemma coeff_ppoly_top (b : ℕ) (a : ℚ) (f : PowerSeries ℚ) (hb : 1 ≤ b) :
    (ppoly b a f).coeff (b - 1) = PowerSeries.coeff (b - 1) f := by
  unfold ppoly
  rw [finsetSum_coeff, Finset.sum_eq_single (b - 1)]
  · rw [coeff_C_mul, coeff_X_sub_C_pow_self, mul_one]
  · intro j hj hne
    rw [coeff_C_mul]
    have hj' := mem_range.mp hj
    have : ((X - C a) ^ j).coeff (b - 1) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
      omega
    rw [this, mul_zero]
  · intro h
    exact absurd (mem_range.mpr (by omega)) h

/-- **Residues sum to zero.** If `deg N + 1 < Σ B_k`, then `Σ_k [X^{B_k - 1}] f_k = 0`
(the terms with `B_k = 0` are read as `0`). -/
theorem pf_top_coeff (N : ℚ[X]) (hinj : Set.InjOn c s) (hdeg : N.natDegree + 1 < ∑ k ∈ s, B k)
    (w : ι → PowerSeries ℚ) (hw : ∀ k ∈ s, w k * shiftPS (c k) (cof s c B k) = 1) :
    ∑ k ∈ s, (if 1 ≤ B k then PowerSeries.coeff (B k - 1) (shiftPS (c k) N * w k) else 0)
      = 0 := by
  have hid := pf_identity s c B N hinj (by omega) w hw
  have h0 : N.coeff (∑ k ∈ s, B k - 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hid, finsetSum_coeff] at h0
  refine Eq.trans (sum_congr rfl (fun k hk => ?_)) h0
  split_ifs with hb
  · have hsum := sum_erase_add s B hk
    have he : ∑ k ∈ s, B k - 1 = (B k - 1) + ∑ k' ∈ s.erase k, B k' := by omega
    rw [he, coeff_mul_add_eq_of_natDegree_le (natDegree_ppoly_le _ _ _) (natDegree_cof s c B k).le,
      coeff_ppoly_top _ _ _ hb, ← natDegree_cof s c B k, (monic_cof s c B k).coeff_natDegree,
      mul_one]
  · have hb0 : B k = 0 := by omega
    simp [ppoly, hb0]

end ZetaIrr.PF
