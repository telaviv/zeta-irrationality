/-
# The concrete Z7 rational function `R_n` in the complex plane

For `RC m` (the complex extension of `Z7.R m`, `Gamma.lean`):
* block bookkeeping: `blkC`, `BkC`, `prod_blocks`, `sum_BkC : Σ_{k ≤ n} B_k = 3294(m+1) + 18`,
  `BkC_zero : B_0 = 0` (no block contains `0`);
* `RC_eq`: `RC m = NC m / DC m` with `NC = (2z+n) Π_{l=1}^{rn} (z-l)⁵ Π_{l=n+1}^{(1+r)n} (z+l)⁵`,
  `DC = Π_{k ≤ n} (z + k)^{B_k}`;
* holomorphy off the poles `-k`, `1 ≤ k ≤ n` (`RC_differentiableOn`), and of all derivatives
  `RCd m j = deriv^[j] (RC m)`;
* `RCd_re_eq`: `Re R_n⁽ʲ⁾(t) = (Z7.R m)⁽ʲ⁾(t)` for real `t > -1`;
* `RCd_conj`: `R_n⁽ʲ⁾(z̄) = conj R_n⁽ʲ⁾(z)`;
* `RCd4_nat_zero`: `R_n⁗(t) = 0` for integers `1 ≤ t ≤ 220(m+1)` (zeros of order 5).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Analytic.Gamma
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Finset Filter Topology Metric
open ZetaIrr.Fam.Analytic

/-! ### Block bookkeeping -/

/-- The index interval of block `b = (k, m_j)`: `[3k(m+1), n - 3k(m+1)]`. -/
def blkC (m : ℕ) (b : ℕ × ℕ) : Finset ℕ := Icc (3 * b.1 * (m + 1)) (Z7.nOf m - 3 * b.1 * (m + 1))

/-- The pole multiplicity `B_k` at `-k`. -/
def BkC (m k : ℕ) : ℕ := (Z7.blocks.map (fun b => if k ∈ blkC m b then b.2 else 0)).sum

lemma blkC_subset (m : ℕ) : ∀ b ∈ Z7.blocks, blkC m b ⊆ range (Z7.nOf m + 1) := by
  intro b _ k hk
  simp only [blkC, Finset.mem_Icc] at hk
  simp only [Finset.mem_range]
  omega

lemma prod_blocks {M : Type*} [CommMonoid M] (m : ℕ) (x : ℕ → M) :
    (Z7.blocks.map (fun b => (∏ k ∈ blkC m b, x k) ^ b.2)).prod
      = ∏ k ∈ range (Z7.nOf m + 1), x k ^ BkC m k := by
  rw [prod_list_blocks x (blkC m) _ Z7.blocks (blkC_subset m)]
  rfl

/-- `Σ_{k ≤ n} B_k = 3294(m+1) + 18`. -/
lemma sum_BkC (m : ℕ) : ∑ k ∈ range (Z7.nOf m + 1), BkC m k = 3294 * (m + 1) + 18 := by
  simp only [BkC]
  rw [sum_list_blocks (blkC m) _ Z7.blocks (blkC_subset m)]
  simp only [Z7.blocks, blkC, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.card_Icc, Z7.nOf]
  omega

/-- No block contains `0`. -/
lemma BkC_zero (m : ℕ) : BkC m 0 = 0 := by
  unfold BkC
  have h : ∀ b ∈ Z7.blocks, (if (0 : ℕ) ∈ blkC m b then b.2 else 0) = 0 := by
    intro b hb
    have h1 := (Z7.blocks_bounds b hb).1
    have hpos : 0 < 3 * b.1 * (m + 1) := Nat.mul_pos (Nat.mul_pos (by norm_num) h1) (Nat.succ_pos m)
    have : ¬ ((0 : ℕ) ∈ blkC m b) := by
      simp only [blkC, Finset.mem_Icc, not_and]
      intro h0; omega
    simp [this]
  rw [List.map_congr_left h]
  simp

/-- Numerator of `RC m`. -/
noncomputable def NC (m : ℕ) (z : ℂ) : ℂ :=
  (2 * z + (Z7.nOf m : ℂ)) * (∏ l ∈ Icc 1 (220 * (m + 1)), (z - (l : ℂ)) ^ 5) *
    (∏ l ∈ Icc (Z7.nOf m + 1) (460 * (m + 1)), (z + (l : ℂ)) ^ 5)

/-- Denominator of `RC m`. -/
noncomputable def DC (m : ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ range (Z7.nOf m + 1), (z + (k : ℂ)) ^ BkC m k

lemma RC_eq (m : ℕ) (z : ℂ) : RC m z = NC m z / DC m z := by
  unfold RC NC DC
  rw [← prod_blocks m (fun k => z + (k : ℂ))]
  rfl

/-- The poles `-k`, `1 ≤ k ≤ n`. -/
def poles (m : ℕ) : Set ℂ := {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ Z7.nOf m ∧ z = -(k : ℂ)}

lemma re_le_of_mem_poles {m : ℕ} {z : ℂ} (hz : z ∈ poles m) : z.re ≤ -1 := by
  obtain ⟨k, hk, _, rfl⟩ := hz
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simp
  linarith

lemma isOpen_compl_poles (m : ℕ) : IsOpen (poles m)ᶜ := by
  have hfin : (poles m).Finite := by
    have : poles m ⊆ (fun k : ℕ => -(k : ℂ)) '' {k | k ≤ Z7.nOf m} := by
      rintro z ⟨k, _, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    exact ((Set.finite_le_nat _).image _).subset this
  exact hfin.isClosed.isOpen_compl

lemma DC_ne_zero (m : ℕ) {z : ℂ} (hz : z ∉ poles m) : DC m z ≠ 0 := by
  unfold DC
  rw [prod_ne_zero_iff]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [BkC_zero, pow_zero]; exact one_ne_zero
  refine pow_ne_zero _ (fun h0 => hz ⟨k, hk0, Nat.lt_succ_iff.1 (mem_range.1 hk), ?_⟩)
  linear_combination h0

lemma NC_differentiable (m : ℕ) : Differentiable ℂ (NC m) := by
  unfold NC
  fun_prop

lemma DC_differentiable (m : ℕ) : Differentiable ℂ (DC m) := by
  unfold DC
  fun_prop

lemma RC_differentiableOn (m : ℕ) : DifferentiableOn ℂ (RC m) (poles m)ᶜ := by
  intro z hz
  have h : RC m = fun z => NC m z / DC m z := funext (RC_eq m)
  rw [h]
  exact ((NC_differentiable m z).div (DC_differentiable m z)
    (DC_ne_zero m hz)).differentiableWithinAt

lemma mem_compl_poles_of_re {m : ℕ} {z : ℂ} (hz : -1 < z.re) : z ∈ (poles m)ᶜ := fun hp => by
  have := re_le_of_mem_poles hp; linarith

/-- The complex derivatives `R_n⁽ʲ⁾`. -/
noncomputable def RCd (m j : ℕ) : ℂ → ℂ := deriv^[j] (RC m)

lemma RCd_differentiableOn (m j : ℕ) : DifferentiableOn ℂ (RCd m j) (poles m)ᶜ :=
  differentiableOn_iterate_deriv (isOpen_compl_poles m) (RC_differentiableOn m) j

lemma RCd_differentiableAt (m j : ℕ) {z : ℂ} (hz : z ∉ poles m) :
    DifferentiableAt ℂ (RCd m j) z :=
  (RCd_differentiableOn m j).differentiableAt ((isOpen_compl_poles m).mem_nhds hz)

lemma hasDerivAt_RCd (m j : ℕ) {z : ℂ} (hz : z ∉ poles m) :
    HasDerivAt (RCd m j) (RCd m (j + 1) z) z := by
  have h := (RCd_differentiableAt m j hz).hasDerivAt
  unfold RCd at h ⊢
  rwa [Function.iterate_succ_apply']

/-- `Re R_n⁽ʲ⁾(t) = (Z7.R m)⁽ʲ⁾(t)` for real `t > -1`. -/
lemma RCd_re_eq (m j : ℕ) {t : ℝ} (ht : -1 < t) :
    (RCd m j t).re = iteratedDeriv j (Z7.R m) t := by
  induction j generalizing t with
  | zero =>
    simp [RCd, RC_ofReal]
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv j (Z7.R m) =ᶠ[𝓝 t] fun x : ℝ => (RCd m j x).re := by
      filter_upwards [lt_mem_nhds ht] with x hx using (ih hx).symm
    rw [heq.deriv_eq]
    have hd := (hasDerivAt_RCd m j (mem_compl_poles_of_re (z := (t : ℂ)) (by simpa using ht)))
    exact hd.real_of_complex.deriv.symm

lemma conj_mem_compl_poles (m : ℕ) {z : ℂ} (hz : z ∈ (poles m)ᶜ) :
    (starRingEnd ℂ) z ∈ (poles m)ᶜ := by
  rintro ⟨k, hk1, hk, h⟩
  apply hz
  refine ⟨k, hk1, hk, ?_⟩
  have := congrArg (starRingEnd ℂ) h
  rw [Complex.conj_conj] at this
  rw [this]
  simp

lemma RC_conj (m : ℕ) (z : ℂ) : RC m ((starRingEnd ℂ) z) = (starRingEnd ℂ) (RC m z) := by
  rw [RC_eq, RC_eq, map_div₀]
  unfold NC DC
  simp [map_prod, map_pow, map_mul, map_add, map_sub, map_natCast, map_ofNat]

lemma RCd_conj (m j : ℕ) {z : ℂ} (hz : z ∉ poles m) :
    RCd m j ((starRingEnd ℂ) z) = (starRingEnd ℂ) (RCd m j z) :=
  iterate_deriv_conj_symm (isOpen_compl_poles m) (fun z hz => conj_mem_compl_poles m hz)
    (RC_differentiableOn m) (fun z _ => RC_conj m z) j z hz

/-- `R_n⁽ʲ⁾(t) = 0` for `j ≤ 4` and integers `1 ≤ t ≤ 220(m+1)` (zeros of order 5). -/
lemma RCd_nat_zero (m t j : ℕ) (hj : j < 5) (ht1 : 1 ≤ t) (ht : t ≤ 220 * (m + 1)) :
    RCd m j t = 0 := by
  have htZ : t ∈ Icc 1 (220 * (m + 1)) := mem_Icc.2 ⟨ht1, ht⟩
  set h : ℂ → ℂ := fun z => (2 * z + (Z7.nOf m : ℂ)) *
    (∏ l ∈ (Icc 1 (220 * (m + 1))).erase t, (z - (l : ℂ)) ^ 5) *
    (∏ l ∈ Icc (Z7.nOf m + 1) (460 * (m + 1)), (z + (l : ℂ)) ^ 5) / DC m z with hh
  have hball : ∀ z ∈ ball (t : ℂ) (1 / 2), z ∉ poles m := by
    intro z hz hp
    have h1 := re_le_of_mem_poles hp
    rw [mem_ball, dist_eq_norm] at hz
    have h2 := Complex.abs_re_le_norm (z - t)
    have : (z - t).re = z.re - t := by simp
    rw [this] at h2
    have := (abs_lt.1 (h2.trans_lt hz)).1
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    linarith
  refine iterate_deriv_eq_zero_of_pow (g := RC m) (h := h) (r := 1 / 2) (p := 5) (by norm_num)
    hj ?_ ?_
  · intro z hz
    have hne := DC_ne_zero m (hball z hz)
    rw [hh]
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.div ?_ (DC_differentiable m z) hne
    fun_prop
  · intro z _
    rw [RC_eq, hh, NC]
    rw [← mul_prod_erase _ _ htZ]
    ring

end ZetaIrr.Z7.Analytic
