/-
# Partial fractions with Taylor-coefficient data (general theory)

For pairwise distinct centres `c k` (`k ∈ s`), multiplicities `B k`, and a polynomial `N` over `ℚ`
with
`deg N < Σ B k`, put `D = Π_k (X - c_k)^{B_k}` and `Q_k = D / (X - c_k)^{B_k}` (the *cofactor*).
If `w k` is a power series inverse of `Q_k(c_k + X)`, and `f_k := N(c_k + X) · w k`, then

  `N / D = Σ_k Σ_{j < B_k} [X^j] f_k · (t - c_k)^j / (t - c_k)^{B_k}`.

This is PROOF_BETA §3 ("a_{i,k} = [ε^{B_k - i}] f_k(t₀ + ε)") in general form.

* `pf_identity`: the polynomial identity `N = Σ_k P_k Q_k`;
* `pf_eval`, `pf_eval'`: the evaluated identity at real `t` off the centres;
* `pf_symm`: behaviour of the coefficients under a mirror symmetry `t ↦ α - t`.

Status: complete (no `sorry`).
-/
import Mathlib

namespace ZetaIrr.PF

open Polynomial Finset

/-- `shiftPS a p = p(X + a)`, as a power series. -/
noncomputable def shiftPS (a : ℚ) : ℚ[X] →+* PowerSeries ℚ :=
  (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.compRingHom (X + C a))

lemma shiftPS_apply (a : ℚ) (p : ℚ[X]) :
    shiftPS a p = ((p.comp (X + C a) : ℚ[X]) : PowerSeries ℚ) := rfl

lemma shiftPS_X_sub_C (a b : ℚ) :
    shiftPS a (X - C b) = PowerSeries.C (a - b) + PowerSeries.X := by
  rw [shiftPS_apply]
  simp only [sub_comp, X_comp, C_comp]
  rw [show (X + C a - C b : ℚ[X]) = C (a - b) + X by rw [C_sub]; ring]
  rw [Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_X]

lemma shiftPS_C (a b : ℚ) : shiftPS a (C b) = PowerSeries.C b := by
  rw [shiftPS_apply, C_comp, Polynomial.coe_C]

lemma shiftPS_X (a : ℚ) : shiftPS a X = PowerSeries.C a + PowerSeries.X := by
  rw [shiftPS_apply, X_comp, Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_X, add_comm]

/-- Reflection of divisibility: if `E(a + X)` vanishes to order `b` then `(X - a)^b ∣ E`. -/
lemma dvd_of_shiftPS {E : ℚ[X]} {a : ℚ} {b : ℕ}
    (h : ∀ j < b, PowerSeries.coeff j (shiftPS a E) = 0) : (X - C a) ^ b ∣ E := by
  have h1 : X ^ b ∣ E.comp (X + C a) := by
    refine X_pow_dvd_iff.mpr (fun d hd => ?_)
    have := h d hd
    rwa [shiftPS_apply, Polynomial.coeff_coe] at this
  obtain ⟨G, hG⟩ := h1
  have h2 : E = (E.comp (X + C a)).comp (X - C a) := by
    rw [comp_assoc]
    simp
  rw [h2, hG, mul_comp, pow_comp, X_comp]
  exact dvd_mul_right _ _

/-! ### The principal-part polynomial -/

/-- `ppoly b a f = Σ_{j<b} [X^j]f · (X - a)^j`. -/
noncomputable def ppoly (b : ℕ) (a : ℚ) (f : PowerSeries ℚ) : ℚ[X] :=
  ∑ j ∈ range b, C (PowerSeries.coeff j f) * (X - C a) ^ j

lemma coeff_shiftPS_ppoly (b : ℕ) (a : ℚ) (f : PowerSeries ℚ) (d : ℕ) :
    PowerSeries.coeff d (shiftPS a (ppoly b a f))
      = if d < b then PowerSeries.coeff d f else 0 := by
  have h : shiftPS a (X - C a) = PowerSeries.X := by
    rw [shiftPS_X_sub_C, sub_self, map_zero, zero_add]
  simp only [ppoly, map_sum, map_mul, map_pow, h, shiftPS_C, map_sum,
    PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

lemma natDegree_ppoly_le (b : ℕ) (a : ℚ) (f : PowerSeries ℚ) :
    (ppoly b a f).natDegree ≤ b - 1 := by
  unfold ppoly
  refine natDegree_sum_le_of_forall_le _ _ (fun j hj => ?_)
  have hj' : j < b := Finset.mem_range.mp hj
  refine (natDegree_C_mul_le _ _).trans (natDegree_pow_le.trans ?_)
  rw [natDegree_X_sub_C]
  omega

/-- The local step: `N - P·Q` vanishes to order `b` at `a` when `P` is the truncation of
`N(a+X) / Q(a+X)`. -/
lemma local_dvd (N Q : ℚ[X]) (a : ℚ) (b : ℕ) (w : PowerSeries ℚ)
    (hw : w * shiftPS a Q = 1) :
    (X - C a) ^ b ∣ N - ppoly b a (shiftPS a N * w) * Q := by
  apply dvd_of_shiftPS
  intro j hj
  set f := shiftPS a N * w with hf
  have hN : shiftPS a N = f * shiftPS a Q := by
    rw [hf, mul_assoc, hw, mul_one]
  rw [map_sub, map_mul, hN, ← sub_mul, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  have hp' : p.1 + p.2 = j := by simpa using hp
  rw [map_sub, coeff_shiftPS_ppoly]
  simp [show p.1 < b by omega]

/-! ### The polynomial identity -/

variable {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℚ) (B : ι → ℕ)

/-- The cofactor `Q_k = Π_{k' ≠ k} (X - c_{k'})^{B_{k'}}`. -/
noncomputable def cof (k : ι) : ℚ[X] := ∏ k' ∈ s.erase k, (X - C (c k')) ^ (B k')

/-- The denominator `D = Π_k (X - c_k)^{B_k}`. -/
noncomputable def den : ℚ[X] := ∏ k ∈ s, (X - C (c k)) ^ (B k)

lemma den_eq {k : ι} (hk : k ∈ s) : den s c B = (X - C (c k)) ^ (B k) * cof s c B k :=
  (Finset.mul_prod_erase s _ hk).symm

omit [DecidableEq ι] in
lemma natDegree_den : (den s c B).natDegree = ∑ k ∈ s, B k := by
  unfold den
  rw [natDegree_prod_of_monic _ _ (fun k _ => (monic_X_sub_C _).pow _)]
  simp

lemma natDegree_cof_le (k : ι) : (cof s c B k).natDegree ≤ ∑ k' ∈ s.erase k, B k' := by
  unfold cof
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun k' _ => ?_))
  refine natDegree_pow_le.trans ?_
  simp

/-- **Partial-fraction identity (polynomial form).** -/
theorem pf_identity (N : ℚ[X]) (hinj : Set.InjOn c s) (hdeg : N.natDegree < ∑ k ∈ s, B k)
    (w : ι → PowerSeries ℚ) (hw : ∀ k ∈ s, w k * shiftPS (c k) (cof s c B k) = 1) :
    N = ∑ k ∈ s, ppoly (B k) (c k) (shiftPS (c k) N * w k) * cof s c B k := by
  set E := N - ∑ k ∈ s, ppoly (B k) (c k) (shiftPS (c k) N * w k) * cof s c B k with hE
  suffices E = 0 by rwa [sub_eq_zero] at this
  have hdvd : den s c B ∣ E := by
    refine Finset.prod_dvd_of_coprime (fun k hk k' hk' hne => ?_) (fun k hk => ?_)
    · refine IsCoprime.pow (isCoprime_X_sub_C_of_isUnit_sub ?_)
      exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (fun h => hne (hinj hk hk' h)))
    · have hsplit : E = (N - ppoly (B k) (c k) (shiftPS (c k) N * w k) * cof s c B k)
          - ∑ k' ∈ s.erase k, ppoly (B k') (c k') (shiftPS (c k') N * w k') * cof s c B k' := by
        rw [hE, ← Finset.add_sum_erase s _ hk]
        ring
      rw [hsplit]
      refine dvd_sub (local_dvd _ _ _ _ _ (hw k hk)) (Finset.dvd_sum (fun k' hk' => ?_))
      refine dvd_mul_of_dvd_right ?_ _
      unfold cof
      have : k ∈ s.erase k' := by
        rw [Finset.mem_erase]
        exact ⟨(Finset.ne_of_mem_erase hk').symm, hk⟩
      exact Finset.dvd_prod_of_mem (fun k'' => (X - C (c k'')) ^ (B k'')) this
  have hnat : E.natDegree < (den s c B).natDegree := by
    rw [natDegree_den]
    refine lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hdeg ?_)
    have hpos : 0 < ∑ k ∈ s, B k := lt_of_le_of_lt (Nat.zero_le _) hdeg
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := ∑ k ∈ s, B k - 1)
      (fun k hk => ?_)) (by omega)
    have hsum := Finset.sum_erase_add s B hk
    rcases Nat.eq_zero_or_pos (B k) with h0 | hpos'
    · simp [ppoly, h0]
    · refine (natDegree_mul_le).trans ?_
      have h1 := natDegree_ppoly_le (B k) (c k) (shiftPS (c k) N * w k)
      have h2 := natDegree_cof_le s c B k
      omega
  exact eq_zero_of_dvd_of_natDegree_lt hdvd hnat

/-! ### Evaluation at real points -/

omit [DecidableEq ι] in
lemma aeval_den_ne_zero {t : ℝ} (ht : ∀ k ∈ s, t ≠ (c k : ℝ)) : aeval t (den s c B) ≠ 0 := by
  unfold den
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
  simp only [map_pow, map_sub, aeval_X, aeval_C, eq_ratCast]
  exact pow_ne_zero _ (sub_ne_zero.mpr (ht k hk))

lemma aeval_cof_ne_zero {t : ℝ} (ht : ∀ k ∈ s, t ≠ (c k : ℝ)) (k : ι) :
    aeval t (cof s c B k) ≠ 0 := by
  unfold cof
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr (fun k' hk' => ?_)
  simp only [map_pow, map_sub, aeval_X, aeval_C, eq_ratCast]
  exact pow_ne_zero _ (sub_ne_zero.mpr (ht k' (Finset.mem_of_mem_erase hk')))

/-- **Partial fractions, evaluated.** -/
theorem pf_eval (N : ℚ[X]) (hinj : Set.InjOn c s) (hdeg : N.natDegree < ∑ k ∈ s, B k)
    (w : ι → PowerSeries ℚ) (hw : ∀ k ∈ s, w k * shiftPS (c k) (cof s c B k) = 1)
    (t : ℝ) (ht : ∀ k ∈ s, t ≠ (c k : ℝ)) :
    aeval t N / aeval t (den s c B)
      = ∑ k ∈ s, ∑ j ∈ range (B k),
          ((PowerSeries.coeff j (shiftPS (c k) N * w k) : ℚ) : ℝ) * (t - c k) ^ j
            / (t - c k) ^ (B k) := by
  conv_lhs => rw [pf_identity s c B N hinj hdeg w hw]
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [den_eq s c B hk, map_mul, map_mul,
    mul_div_mul_right _ _ (aeval_cof_ne_zero s c B ht k)]
  simp only [ppoly, map_sum, map_mul, map_pow, map_sub, aeval_X, aeval_C, eq_ratCast,
    Finset.sum_div]

/-- Reindexing `j = b - i`. -/
lemma sum_range_div_pow (b : ℕ) (x : ℕ → ℝ) (y : ℝ) (hy : y ≠ 0) :
    ∑ j ∈ range b, x j * y ^ j / y ^ b = ∑ i ∈ Icc 1 b, x (b - i) * (y ^ i)⁻¹ := by
  refine Finset.sum_nbij' (fun j => b - j) (fun i => b - i) ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Finset.mem_range, Finset.mem_Icc]
  · intro j hj; omega
  · intro i hi; omega
  · intro j hj; omega
  · intro i hi; omega
  · intro j hj
    have hb : b = j + (b - j) := by omega
    rw [show b - (b - j) = j by omega]
    conv_lhs => rw [hb, pow_add]
    field_simp

/-- **Partial fractions, evaluated (PFData form).** -/
theorem pf_eval' (N : ℚ[X]) (hinj : Set.InjOn c s) (hdeg : N.natDegree < ∑ k ∈ s, B k)
    (w : ι → PowerSeries ℚ) (hw : ∀ k ∈ s, w k * shiftPS (c k) (cof s c B k) = 1)
    (t : ℝ) (ht : ∀ k ∈ s, t ≠ (c k : ℝ)) :
    aeval t N / aeval t (den s c B)
      = ∑ k ∈ s, ∑ i ∈ Icc 1 (B k),
          ((PowerSeries.coeff (B k - i) (shiftPS (c k) N * w k) : ℚ) : ℝ) * ((t - c k) ^ i)⁻¹ := by
  rw [pf_eval s c B N hinj hdeg w hw t ht]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  exact sum_range_div_pow (B k) (fun j => ((PowerSeries.coeff j (shiftPS (c k) N * w k) : ℚ) : ℝ))
    _ (sub_ne_zero.mpr (ht k hk))

/-! ### Mirror symmetry -/

lemma rescale_C (a x : ℚ) : PowerSeries.rescale a (PowerSeries.C x) = PowerSeries.C x := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · simp [h]
  · simp

omit [DecidableEq ι] in
lemma rescale_shiftPS (a : ℚ) (p : ℚ[X]) :
    PowerSeries.rescale (-1) (shiftPS a p) = ((p.comp (C a - X) : ℚ[X]) : PowerSeries ℚ) := by
  have h : (PowerSeries.rescale (-1 : ℚ)).comp (shiftPS a)
      = (Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.compRingHom (C a - X)) := by
    refine Polynomial.ringHom_ext (fun x => ?_) ?_
    · change PowerSeries.rescale (-1) (shiftPS a (C x))
          = Polynomial.coeToPowerSeries.ringHom ((C x).comp (C a - X))
      rw [shiftPS_C, rescale_C, C_comp, coeToPowerSeries.ringHom_apply, coe_C]
    · change PowerSeries.rescale (-1) (shiftPS a X)
          = Polynomial.coeToPowerSeries.ringHom (X.comp (C a - X))
      rw [X_comp, map_sub, coeToPowerSeries.ringHom_apply, coeToPowerSeries.ringHom_apply,
        coe_C, coe_X, shiftPS_X, map_add, rescale_C, PowerSeries.rescale_neg_one_X]
      ring
  exact RingHom.congr_fun h p

/-- The cofactor under the mirror map. -/
lemma cof_comp_mirror (π : ι → ι) (α : ℚ)
    (hπs : ∀ k ∈ s, π k ∈ s) (hππ : ∀ k ∈ s, π (π k) = k)
    (hc : ∀ k ∈ s, c (π k) = α - c k) (hB : ∀ k ∈ s, B (π k) = B k)
    (k : ι) (hk : k ∈ s) :
    (cof s c B k).comp (C α - X)
      = C ((-1) ^ (∑ k' ∈ s.erase k, B k')) * cof s c B (π k) := by
  have h1 : (cof s c B k).comp (C α - X)
      = ∏ k' ∈ s.erase k, (C ((-1) ^ B k') * (X - C (c (π k'))) ^ B k') := by
    change Polynomial.compRingHom (C α - X) (cof s c B k) = _
    unfold cof
    rw [map_prod]
    refine Finset.prod_congr rfl (fun k' hk' => ?_)
    have hk's : k' ∈ s := Finset.mem_of_mem_erase hk'
    rw [map_pow, hc k' hk's]
    change ((X - C (c k')).comp (C α - X)) ^ B k' = _
    rw [sub_comp, X_comp, C_comp, map_pow, ← mul_pow]
    congr 1
    rw [C_sub, map_neg, map_one]
    ring
  rw [h1, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
  congr 1
  unfold cof
  refine Finset.prod_nbij' π π ?_ ?_ ?_ ?_ ?_
  · intro k' hk'
    simp only [Finset.mem_erase] at hk' ⊢
    refine ⟨fun h => hk'.1 ?_, hπs k' hk'.2⟩
    rw [← hππ k' hk'.2, h, hππ k hk]
  · intro k' hk'
    simp only [Finset.mem_erase] at hk' ⊢
    refine ⟨fun h => hk'.1 ?_, hπs k' hk'.2⟩
    rw [← h, hππ k' hk'.2]
  · intro k' hk'
    simp only [Finset.mem_erase] at hk'
    exact hππ k' hk'.2
  · intro k' hk'
    simp only [Finset.mem_erase] at hk'
    exact hππ k' hk'.2
  · intro k' hk'
    rw [hB k' (Finset.mem_of_mem_erase hk')]

/-- **Mirror symmetry of the coefficients.** -/
theorem pf_symm (N : ℚ[X]) (π : ι → ι) (α ε : ℚ)
    (hπs : ∀ k ∈ s, π k ∈ s) (hππ : ∀ k ∈ s, π (π k) = k)
    (hc : ∀ k ∈ s, c (π k) = α - c k) (hB : ∀ k ∈ s, B (π k) = B k)
    (hN : N.comp (C α - X) = C ε * N) (hε : ε * ε = 1)
    (w : ι → PowerSeries ℚ) (hw : ∀ k ∈ s, w k * shiftPS (c k) (cof s c B k) = 1)
    (k : ι) (hk : k ∈ s) (j : ℕ) :
    PowerSeries.coeff j (shiftPS (c (π k)) N * w (π k))
      = ε * (-1) ^ (∑ k' ∈ s.erase k, B k') * (-1) ^ j
          * PowerSeries.coeff j (shiftPS (c k) N * w k) := by
  set σ : ℚ := (-1) ^ (∑ k' ∈ s.erase k, B k') with hσ
  have hσ2 : σ * σ = 1 := by
    rw [hσ, ← mul_pow]; norm_num
  have hcomp : (C (c k) - X : ℚ[X]) = (C α - X).comp (X + C (c (π k))) := by
    rw [sub_comp, X_comp, C_comp, hc k hk, C_sub]
    ring
  have hNs : PowerSeries.rescale (-1) (shiftPS (c k) N)
      = PowerSeries.C ε * shiftPS (c (π k)) N := by
    rw [rescale_shiftPS, hcomp, ← comp_assoc, hN, mul_comp, C_comp, Polynomial.coe_mul, coe_C,
      shiftPS_apply]
  have hQs : PowerSeries.rescale (-1) (shiftPS (c k) (cof s c B k))
      = PowerSeries.C σ * shiftPS (c (π k)) (cof s c B (π k)) := by
    rw [rescale_shiftPS, hcomp, ← comp_assoc,
      cof_comp_mirror s c B π α hπs hππ hc hB k hk, mul_comp, C_comp, Polynomial.coe_mul, coe_C,
      shiftPS_apply]
  have H1 : PowerSeries.rescale (-1) (w k)
      * (PowerSeries.C σ * shiftPS (c (π k)) (cof s c B (π k))) = 1 := by
    rw [← hQs, ← map_mul, hw k hk, map_one]
  have H2 := hw (π k) (hπs k hk)
  have H3 : PowerSeries.C σ * PowerSeries.C σ = (1 : PowerSeries ℚ) := by
    rw [← map_mul, hσ2, map_one]
  have hW : PowerSeries.rescale (-1) (w k) = PowerSeries.C σ * w (π k) := by
    linear_combination (-(PowerSeries.rescale (-1) (w k))) * H2
      + (w (π k) * PowerSeries.C σ) * H1
      - (w (π k) * shiftPS (c (π k)) (cof s c B (π k)) * PowerSeries.rescale (-1) (w k)) * H3
  have hF : PowerSeries.rescale (-1) (shiftPS (c k) N * w k)
      = PowerSeries.C (ε * σ) * (shiftPS (c (π k)) N * w (π k)) := by
    rw [map_mul, hNs, hW, map_mul]
    ring
  have hcoef := congrArg (PowerSeries.coeff j) hF
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C_mul] at hcoef
  have hj2 : ((-1 : ℚ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(ε * σ)) * hcoef
    - PowerSeries.coeff j (shiftPS (c (π k)) N * w (π k)) * hε
    - (PowerSeries.coeff j (shiftPS (c (π k)) N * w (π k)) * ε * ε) * hσ2

/-! ### Derivatives of a rational function -/

/-- The numerator of `(N/D)' = (N'D - ND')/D²`. -/
noncomputable def dnum (N D : ℚ[X]) : ℚ[X] := derivative N * D - N * derivative D

lemma hasDerivAt_ratfun (N D : ℚ[X]) (t : ℝ) (hD : aeval t D ≠ 0) :
    HasDerivAt (fun x => aeval x N / aeval x D) (aeval t (dnum N D) / aeval t (D ^ 2)) t := by
  have := (N.hasDerivAt_aeval t).div (D.hasDerivAt_aeval t) hD
  convert this using 1
  simp [dnum, map_sub, map_mul, map_pow]

/-- A triple zero of `N` at `l` kills the second derivative of `N/D` at `l`. -/
lemma aeval_dnum_dnum_eq_zero (N D M : ℚ[X]) (l : ℚ) (hN : N = (X - C l) ^ 3 * M) :
    aeval (l : ℝ) (dnum (dnum N D) (D ^ 2)) = 0 := by
  subst hN
  simp [dnum, derivative_mul, derivative_pow]

end ZetaIrr.PF
