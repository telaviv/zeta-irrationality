/-
# Expansion lemmas (Lemmas 1–3)

We work with *partial-fraction data*: rational coefficients `a i k` of `(t + k)^(-i)`, for
`1 ≤ i ≤ I` and `0 ≤ k ≤ K`. The rational function is `R t = ∑ₖ ∑ᵢ a i k / (t + k)^i`.

* `Rd j`: the termwise `j`-th derivative, `∑ₖ ∑ᵢ a i k (-1)^j (i)_j (t + k)^(-(i+j))`;
  `hasDerivAt_Rd`: `(Rd j)' = Rd (j+1)` for `t > 0`.
* `iteratedDeriv_eq_of_eqOn`: if `f = Rd 0` on an open set `U`, then `f⁽ʲ⁾ = Rd j` on `U`.
* `tsum_shift` (Lemma 1, series part): `∑_{t≥0} (t + 1 + k)^(-j) = ζ(j) - H_k^{(j)}` for `j ≥ 2`.
* `tsum_R4` (Lemma 1): `∑_{t≥1} R⁗(t) = ρ + ∑_{i=1}^{I} τ_i ζ(i+4)` with `ρ, τ_i ∈ ℚ`,
  `τ_i = (i)_4 ∑ₖ a i k`.
* `tau_eq_zero_of_even` (Lemma 2): under the symmetry `a i (K-k) = (-1)^(i+1) a i k`,
  `τ_i = 0` for even `i`.
* `tsum_R4_odd` (Lemma 3): if moreover `τ_1 = 0`, then
  `∑_{t≥1} R⁗(t) = ρ + ∑_{j=3}^{J} τ_{2j-3} ζ(2j+1)`. `ζ(3)` and `ζ(5)` never occur.
-/
import ZetaIrrational.Defs

namespace ZetaIrr

open Finset
open scoped BigOperators

/-- The rising factorial `(i)_j = i (i+1) ⋯ (i+j-1)` as a rational number. -/
def rise (i j : ℕ) : ℚ := ∏ l ∈ range j, ((i : ℚ) + l)

lemma rise_succ (i j : ℕ) : rise i (j + 1) = rise i j * ((i : ℚ) + j) := by
  simp [rise, prod_range_succ]

lemma rise_four (i : ℕ) : rise i 4 = (i : ℚ) * (i + 1) * (i + 2) * (i + 3) := by
  simp [rise, prod_range_succ]

/-- Partial-fraction data: coefficients `a i k` of `(t + k)^(-i)`, `1 ≤ i ≤ I`, `0 ≤ k ≤ K`. -/
structure PFData where
  I : ℕ
  K : ℕ
  a : ℕ → ℕ → ℚ

namespace PFData

variable (P : PFData)

/-- The termwise `j`-th derivative `∑ₖ ∑ᵢ a i k (-1)^j (i)_j (t + k)^(-(i+j))`. -/
noncomputable def Rd (j : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range (P.K + 1), ∑ i ∈ Icc 1 P.I,
    (P.a i k : ℝ) * ((-1) ^ j * (rise i j : ℝ) * ((t + k) ^ (i + j))⁻¹)

/-- `R t = ∑ₖ ∑ᵢ a i k (t + k)^(-i)`. -/
noncomputable def R (t : ℝ) : ℝ := P.Rd 0 t

lemma R_eq (t : ℝ) :
    P.R t = ∑ k ∈ range (P.K + 1), ∑ i ∈ Icc 1 P.I, (P.a i k : ℝ) * ((t + k) ^ i)⁻¹ := by
  simp [R, Rd, rise]

/-! ### Lemma 1, derivative part -/

/-- `d/dt (t + c)^(-m) = -m (t + c)^(-(m+1))` where `t + c ≠ 0`. -/
lemma hasDerivAt_inv_pow (c t : ℝ) (m : ℕ) (h : t + c ≠ 0) :
    HasDerivAt (fun t => ((t + c) ^ m)⁻¹) (-(m : ℝ) * ((t + c) ^ (m + 1))⁻¹) t := by
  have h1 : HasDerivAt (fun t => t + c) 1 t := (hasDerivAt_id t).add_const c
  have h2 := (h1.fun_pow m).inv (pow_ne_zero m h)
  refine h2.congr_deriv ?_
  rcases m with _ | m
  · simp
  · rw [Nat.add_sub_cancel]
    field_simp
    ring

lemma hasDerivAt_term (b c t : ℝ) (i j : ℕ) (h : t + c ≠ 0) :
    HasDerivAt (fun t => b * ((-1) ^ j * (rise i j : ℝ) * ((t + c) ^ (i + j))⁻¹))
      (b * ((-1) ^ (j + 1) * (rise i (j + 1) : ℝ) * ((t + c) ^ (i + (j + 1)))⁻¹)) t := by
  have h' := ((hasDerivAt_inv_pow c t (i + j) h).const_mul ((-1) ^ j * (rise i j : ℝ))).const_mul b
  refine h'.congr_deriv ?_
  rw [rise_succ]
  push_cast
  ring_nf

lemma shift_ne_zero {t : ℝ} (ht : 0 < t) (k : ℕ) : t + (k : ℝ) ≠ 0 := by
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact ne_of_gt (by linarith)

/-- **Lemma 1 (derivative part).** `(Rd j)' = Rd (j+1)` on `t > 0`. -/
lemma hasDerivAt_Rd (j : ℕ) {t : ℝ} (ht : 0 < t) : HasDerivAt (P.Rd j) (P.Rd (j + 1) t) t :=
  HasDerivAt.fun_sum (fun k _ => HasDerivAt.fun_sum (fun i _ =>
    hasDerivAt_term (P.a i k) (k : ℝ) t i j (shift_ne_zero ht k)))

/-- Iterated derivatives of a function that agrees on an open set with the head of a chain of
derivatives. -/
theorem iteratedDeriv_eq_of_eqOn {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hfg : Set.EqOn f (g 0) U) (hg : ∀ j, ∀ t ∈ U, HasDerivAt (g j) (g (j + 1) t) t) :
    ∀ j, Set.EqOn (iteratedDeriv j f) (g j) U := by
  intro j
  induction j with
  | zero => simpa using hfg
  | succ j ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j f =ᶠ[nhds t] g j :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds ht) ih
    rw [hev.deriv_eq]
    exact (hg j t ht).deriv

/-- If `f = R` on an open set `U ⊆ (0, ∞)`, then `f⁽ʲ⁾ = Rd j` on `U`. -/
theorem iteratedDeriv_eq_Rd {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hUpos : ∀ t ∈ U, 0 < t)
    (hf : Set.EqOn f P.R U) (j : ℕ) : Set.EqOn (iteratedDeriv j f) (P.Rd j) U :=
  iteratedDeriv_eq_of_eqOn hU hf (fun j t ht => P.hasDerivAt_Rd j (hUpos t ht)) j

/-! ### Lemma 1, series part -/

/-- The rational harmonic sums `H_k^{(j)} = ∑_{m=1}^{k} 1/m^j`. -/
def Hq (j k : ℕ) : ℚ := ∑ m ∈ range k, 1 / ((m : ℚ) + 1) ^ j

lemma Hq_cast (j k : ℕ) : (Hq j k : ℝ) = ∑ m ∈ range k, zetaTerm j m := by
  simp [Hq, zetaTerm]

lemma shift_term_eq (j k t : ℕ) :
    ((((t : ℝ) + 1) + k) ^ j)⁻¹ = zetaTerm j (t + k) := by
  rw [zetaTerm]; push_cast; rw [one_div]; ring_nf

lemma summable_shift (j k : ℕ) (hj : 2 ≤ j) :
    Summable (fun t : ℕ => ((((t : ℝ) + 1) + k) ^ j)⁻¹) := by
  have hs : Summable (fun t : ℕ => zetaTerm j (t + k)) :=
    (summable_nat_add_iff k).mpr (summable_zetaTerm hj)
  exact hs.congr (fun t => (shift_term_eq j k t).symm)

/-- **Lemma 1 (series identity).** For `j ≥ 2`, `∑_{t≥0} (t + 1 + k)^(-j) = ζ(j) - H_k^{(j)}`. -/
theorem tsum_shift (j k : ℕ) (hj : 2 ≤ j) :
    ∑' t : ℕ, ((((t : ℝ) + 1) + k) ^ j)⁻¹ = zetaR j - (Hq j k : ℝ) := by
  have hsplit := (summable_zetaTerm hj).sum_add_tsum_nat_add k
  calc ∑' t : ℕ, ((((t : ℝ) + 1) + k) ^ j)⁻¹ = ∑' t : ℕ, zetaTerm j (t + k) := by
        congr 1; ext t; exact shift_term_eq j k t
    _ = zetaR j - (Hq j k : ℝ) := by
        rw [Hq_cast, zetaR, ← hsplit]
        ring

/-! ### Lemma 1: the full expansion -/

/-- `τ_i = (i)_4 ∑ₖ a i k`: the coefficient of `ζ(i+4)`. -/
def tau (i : ℕ) : ℚ := ∑ k ∈ range (P.K + 1), P.a i k * rise i 4

/-- `ρ = -∑ₖ ∑ᵢ a i k (i)_4 H_k^{(i+4)}`: the rational part. -/
def rho : ℚ := -∑ k ∈ range (P.K + 1), ∑ i ∈ Icc 1 P.I, P.a i k * rise i 4 * Hq (i + 4) k

/-- **Lemma 1.** `∑_{t≥0} R⁗(t+1) = ρ + ∑_{i=1}^{I} τ_i ζ(i+4)`. -/
theorem tsum_R4 :
    ∑' t : ℕ, P.Rd 4 ((t : ℝ) + 1)
      = (P.rho : ℝ) + ∑ i ∈ Icc 1 P.I, (P.tau i : ℝ) * zetaR (i + 4) := by
  have hterm : ∀ t : ℕ, P.Rd 4 ((t : ℝ) + 1)
      = ∑ k ∈ range (P.K + 1), ∑ i ∈ Icc 1 P.I,
          (P.a i k : ℝ) * (rise i 4 : ℝ) * (((((t : ℝ) + 1) + k) ^ (i + 4))⁻¹) := by
    intro t
    rw [Rd]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
    norm_num
    ring
  simp_rw [hterm]
  have hsum_i : ∀ k ∈ range (P.K + 1), ∀ i ∈ Icc 1 P.I, Summable (fun t : ℕ =>
      (P.a i k : ℝ) * (rise i 4 : ℝ) * (((((t : ℝ) + 1) + k) ^ (i + 4))⁻¹)) :=
    fun k _ i _ => (summable_shift (i + 4) k (by omega)).mul_left _
  rw [Summable.tsum_finsetSum (fun k hk => summable_sum (fun i hi => hsum_i k hk i hi))]
  have hinner : ∀ k ∈ range (P.K + 1),
      ∑' t : ℕ, ∑ i ∈ Icc 1 P.I, (P.a i k : ℝ) * (rise i 4 : ℝ) *
          (((((t : ℝ) + 1) + k) ^ (i + 4))⁻¹)
        = ∑ i ∈ Icc 1 P.I, (P.a i k : ℝ) * (rise i 4 : ℝ) *
            (zetaR (i + 4) - (Hq (i + 4) k : ℝ)) := by
    intro k hk
    rw [Summable.tsum_finsetSum (fun i hi => hsum_i k hk i hi)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(summable_shift (i + 4) k (by omega)).tsum_mul_left, tsum_shift (i + 4) k (by omega)]
  rw [Finset.sum_congr rfl hinner]
  simp only [rho, tau, Rat.cast_neg, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm (s := Icc 1 P.I)]
  rw [neg_add_eq_sub, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-! ### Lemma 2: symmetry kills the even τ -/

/-- The mirror symmetry `t ↦ -K-t` of Lemma 2 (`deg R` odd), at the level of the
data: `a_{i,K-k} = (-1)^{i+1} a_{i,k}`. -/
def Symmetric : Prop :=
  ∀ i k, k ≤ P.K → P.a i (P.K - k) = (-1) ^ (i + 1) * P.a i k

/-- **Lemma 2.** Under the symmetry, `τ_i = 0` for even `i`. -/
theorem tau_eq_zero_of_even (hsym : P.Symmetric) {i : ℕ} (hi : Even i) : P.tau i = 0 := by
  set S := ∑ k ∈ range (P.K + 1), P.a i k with hS
  have h := Finset.sum_range_reflect (fun k => P.a i k) (P.K + 1)
  simp only [add_tsub_cancel_right] at h
  have hrefl : S = -S := by
    calc S = ∑ k ∈ range (P.K + 1), P.a i (P.K - k) := by rw [hS]; exact h.symm
      _ = ∑ k ∈ range (P.K + 1), -P.a i k := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have hk : k ≤ P.K := by simpa [Nat.lt_succ_iff] using hk
          rw [hsym i k hk, pow_succ, hi.neg_one_pow]
          ring
      _ = -S := by rw [Finset.sum_neg_distrib, hS]
  have hS0 : S = 0 := by linarith
  have : P.tau i = rise i 4 * S := by
    rw [tau, hS, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [this, hS0, mul_zero]

/-! ### Lemma 3: only ζ(7), ζ(9), …, ζ(2J+1) occur -/

/-- `a i k = 0` for `i > I`: the data is supported in `1 ≤ i ≤ I`. -/
def Supported : Prop := ∀ i k, P.I < i → P.a i k = 0

lemma tau_eq_zero_of_gt (hsupp : P.Supported) {i : ℕ} (hi : P.I < i) : P.tau i = 0 := by
  simp [tau, hsupp i _ hi]

/-- **Lemma 3.** For symmetric data supported in `1 ≤ i ≤ I ≤ 2J - 2` with `τ_1 = 0`:
`∑_{t≥1} R⁗(t) = ρ + ∑_{j=3}^{J} τ_{2j-3} ζ(2j+1)`. In particular `ζ(3)` and `ζ(5)` do not
occur. -/
theorem tsum_R4_odd (hsym : P.Symmetric) (hsupp : P.Supported) (htau1 : P.tau 1 = 0) (J : ℕ)
    (hIJ : P.I + 2 ≤ 2 * J) :
    ∑' t : ℕ, P.Rd 4 ((t : ℝ) + 1)
      = (P.rho : ℝ) + ∑ j ∈ Icc 3 J, (P.tau (2 * j - 3) : ℝ) * zetaR (2 * j + 1) := by
  rw [tsum_R4]
  congr 1
  set g : ℕ → ℝ := fun i => (P.tau i : ℝ) * zetaR (i + 4) with hg
  -- extend the range to `Icc 1 (2J-2)` (the extra terms vanish by support)
  have hext : ∑ i ∈ Icc 1 P.I, g i = ∑ i ∈ Icc 1 (2 * J - 2), g i := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega)) (fun i hi hni => ?_)
    have : P.I < i := by simp only [Finset.mem_Icc] at hi hni; omega
    simp [hg, tau_eq_zero_of_gt P hsupp this]
  rw [hext]
  -- keep only the odd indices `i ≥ 3`
  have hodd : ∑ i ∈ Icc 1 (2 * J - 2) with (Odd i ∧ 3 ≤ i), g i
      = ∑ i ∈ Icc 1 (2 * J - 2), g i := by
    refine Finset.sum_filter_of_ne (fun i _ hne => ?_)
    by_contra hcon
    rcases not_and_or.mp hcon with hev | h3
    · exact hne (by simp [hg, tau_eq_zero_of_even P hsym (Nat.not_odd_iff_even.mp hev)])
    · have hi1 : i = 1 ∨ i = 2 ∨ i = 0 := by omega
      rcases hi1 with rfl | rfl | rfl
      · exact hne (by simp [hg, htau1])
      · exact hne (by simp [hg, tau_eq_zero_of_even P hsym even_two])
      · exact hne (by simp [hg, tau_eq_zero_of_even P hsym ⟨0, rfl⟩])
  rw [← hodd]
  -- reindex the odd indices `i = 2j - 3`, `3 ≤ j ≤ J`
  have himg : (Icc 1 (2 * J - 2)).filter (fun i => Odd i ∧ 3 ≤ i)
      = (Icc 3 J).image (fun j => 2 * j - 3) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨m, hm⟩, h3⟩
      exact ⟨m + 2, by omega, by omega⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨j - 2, by omega⟩, by omega⟩
  rw [himg, Finset.sum_image (fun j1 hj1 j2 hj2 h => by
    simp only [Finset.coe_Icc, Set.mem_Icc] at hj1 hj2
    have h' : 2 * j1 - 3 = 2 * j2 - 3 := h
    omega)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  simp only [Finset.mem_Icc] at hj
  simp only [hg]
  congr 2
  omega

end PFData

end ZetaIrr
