/-
# Size of `D_n` at the small primes (Lemma 4, instance Z7)

With `n = 240(m+1)`, `𝒩 = 700(m+1)+1`, `Λ_p = ⌊log_p 𝒩⌋`, `G = 547/120`:

* `zero_sum_ge`: each zero run is a product of `rn = 220(m+1)` consecutive nonzero integers, so
  `(p-1) Σ_z v_p(k+z) ≥ 440(m+1) - 2(p-1)(Λ_p+1)`;
* `neg_nuSmall_le`: `(p-1)(-ν_p(k)) ≤ 1094(m+1) + 18 + 46(p-1)(Λ_p+1)` (the pole products
  contribute `Σ_k B_k = 3294(m+1) + 18`, and `3294 - 5·440 = 1094 = 240 G`);
* `Esmall_sub_le`: `(p-1)(E_p - G v_p(n!)) ≤ 18 + 73(p-1)(Λ_p+1)`;
* `small_primes_sum_le`: `Σ_{p ≤ √𝒩, p prime} (E_p - G v_p(n!)) log p ≤ 182 ⌊√𝒩⌋ log 𝒩`, so this
  part is `O(√n log n) = o(n)`. The count covers every prime `p ≤ √𝒩`, including `p = 2, 3`.
-/
import ZetaIrrational.Z7.Arith.Integrality
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.unusedSectionVars false

set_option maxRecDepth 8192

namespace ZetaIrr.Z7.Arith

open Finset ZetaIrr.Arith

/-! ### Helpers -/

lemma sum_Zs (m : ℕ) (f : ℤ → ℤ) : ∑ z ∈ Zs m, f z
    = ∑ l ∈ Icc 1 (220 * (m + 1)), f (l : ℤ) + ∑ l ∈ Icc (nOf m + 1) (460 * (m + 1)), f (-(l : ℤ)) := by
  rw [Zs, sum_union (Zs_disjoint m), sum_image (fun a _ b _ h => by exact_mod_cast h),
    sum_image (fun a _ b _ h => by simpa using h)]

lemma list_bound {ι : Type*} (l : List ι) (w X Y : ι → ℤ) (c : ℤ) (hw : ∀ b ∈ l, 0 ≤ w b)
    (h : ∀ b ∈ l, c * X b ≤ Y b) :
    c * (l.map (fun b => w b * X b)).sum ≤ (l.map (fun b => w b * Y b)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
      (fun b hb => h b (List.mem_cons_of_mem a hb))
    have h3 := hw a List.mem_cons_self
    nlinarith

lemma card_blk (m : ℕ) (b : ℕ × ℕ) (hb : b ∈ blocks) :
    ((#(blk m b) : ℕ) : ℤ) = 240 * ((m : ℤ) + 1) - 6 * b.1 * ((m : ℤ) + 1) + 1 := by
  have hb1 : b.1 ≤ 18 := blocks_fst_le b hb
  unfold blk nOf
  rw [Nat.card_Icc]
  have h27 := Nat.mul_le_mul_right (m + 1) (show 3 * b.1 ≤ 54 by omega)
  have hX : ((3 * b.1 * (m + 1) : ℕ) : ℤ) = 3 * (b.1 : ℤ) * ((m : ℤ) + 1) := by push_cast; ring
  generalize 3 * b.1 * (m + 1) = X at h27 hX ⊢
  have key : ((240 * (m + 1) - X + 1 - X : ℕ) : ℤ) = 240 * ((m : ℤ) + 1) + 1 - 2 * (X : ℤ) := by
    omega
  rw [key, hX]
  ring

lemma blocks_weighted_card (m : ℕ) (C : ℤ) :
    (blocks.map (fun b => (b.2 : ℤ) * (((#(blk m b) : ℕ) : ℤ) + C))).sum
      = 3294 * ((m : ℤ) + 1) + 18 + 18 * C := by
  rw [List.map_congr_left (fun b hb => by rw [card_blk m b hb])]
  simp [blocks]
  ring

section Small

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Zero products -/

theorem zero_sum_ge (m k : ℕ) (hk : k ≤ nOf m) :
    440 * ((m : ℤ) + 1) - 2 * ((p - 1 : ℕ) : ℤ) * ((Nat.log p (NN m) : ℤ) + 1)
      ≤ ((p - 1 : ℕ) : ℤ) * ∑ z ∈ Zs m, (padicValInt p (zv k z) : ℤ) := by
  have hk' : k ≤ 240 * (m + 1) := hk
  rw [sum_Zs]
  have h1 : ∑ l ∈ Icc 1 (220 * (m + 1)), (padicValInt p (zv k (l : ℤ)) : ℤ)
      = ((∑ d ∈ Icc (k + 1) (k + 220 * (m + 1)), padicValNat p d : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_nbij' (fun l => k + l) (fun d => d - k) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe] at hx; omega
    · intro x _
      congr 1; unfold padicValInt zv; congr 1; omega
  have h2 : ∑ l ∈ Icc (nOf m + 1) (460 * (m + 1)), (padicValInt p (zv k (-(l : ℤ))) : ℤ)
      = ((∑ d ∈ Icc (nOf m + 1 - k) (460 * (m + 1) - k), padicValNat p d : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_nbij' (fun l => l - k) (fun d => d + k) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [mem_Icc, Finset.mem_coe, nOf] at hx hk' ⊢; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe, nOf] at hx hk' ⊢; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe, nOf] at hx; omega
    · intro x hx; simp only [mem_Icc, Finset.mem_coe, nOf] at hx; omega
    · intro x hx
      simp only [mem_Icc, nOf] at hx
      congr 1; unfold padicValInt zv; congr 1; omega
  rw [h1, h2, mul_add]
  have e1 := sub_one_mul_sum_Icc_ge (p := p) (A := k + 1) (B := k + 220 * (m + 1))
    (by omega) (by omega)
  have e2 := sub_one_mul_sum_Icc_ge (p := p) (A := nOf m + 1 - k) (B := 460 * (m + 1) - k)
    (by omega) (by unfold nOf; omega)
  have hl1 : (Nat.log p (k + 220 * (m + 1)) : ℤ) ≤ Nat.log p (NN m) := by
    exact_mod_cast Nat.log_mono_right (by unfold NN; omega)
  have hl2 : (Nat.log p (460 * (m + 1) - k) : ℤ) ≤ Nat.log p (NN m) := by
    exact_mod_cast Nat.log_mono_right (by unfold NN; omega)
  have hp1 : (0 : ℤ) ≤ ((p - 1 : ℕ) : ℤ) := by positivity
  have hA : (((k + 220 * (m + 1) : ℕ) : ℤ) + 1 - ((k + 1 : ℕ) : ℤ))
      + (((460 * (m + 1) - k : ℕ) : ℤ) + 1 - ((nOf m + 1 - k : ℕ) : ℤ))
      = 440 * ((m : ℤ) + 1) := by unfold nOf; omega
  have m1 := mul_le_mul_of_nonneg_left hl1 hp1
  have m2 := mul_le_mul_of_nonneg_left hl2 hp1
  nlinarith

/-! ### Small primes -/

theorem neg_nuSmall_le (m k : ℕ) (hk : k ≤ nOf m) :
    ((p - 1 : ℕ) : ℤ) * (-nuSmall m p k)
      ≤ 1094 * ((m : ℤ) + 1) + 18 + 46 * ((p - 1 : ℕ) : ℤ) * ((Nat.log p (NN m) : ℤ) + 1) := by
  have hnu : nuSmall m p k = 5 * ∑ z ∈ Zs m, (padicValInt p (zv k z) : ℤ)
      - (blocks.map (fun b => (b.2 : ℤ) *
          ∑ k' ∈ (blk m b).erase k, (padicValInt p ((k' : ℤ) - k) : ℤ))).sum := by
    unfold nuSmall etot
    simp only [sum_neg_distrib, mul_neg, list_sum_map_neg, ← mul_sum]
    ring
  rw [hnu]
  have hc0 : (0 : ℤ) ≤ ((p - 1 : ℕ) : ℤ) := by positivity
  have hZ := zero_sum_ge (p := p) m k hk
  have hPl := list_bound blocks (fun b => (b.2 : ℤ))
    (fun b => ∑ k' ∈ (blk m b).erase k, (padicValInt p ((k' : ℤ) - k) : ℤ))
    (fun b => ((#(blk m b) : ℕ) : ℤ)
      + 2 * ((p - 1 : ℕ) : ℤ) * ((Nat.log p (NN m) : ℤ) + 1)) ((p - 1 : ℕ) : ℤ)
    (fun b _ => by positivity)
    (fun b hb => by
      have := pole_sum_le (p := p) (a := 3 * b.1 * (m + 1)) (b := nOf m - 3 * b.1 * (m + 1))
        (k := k) (N := NN m) (by
          have hb1 : b.1 ≤ 18 := blocks_fst_le b hb
          have := Nat.mul_le_mul_right (m + 1) (show 3 * b.1 ≤ 54 by omega)
          unfold NN; nlinarith) (by have := nOf_lt_NN m; omega)
      exact this)
  rw [blocks_weighted_card] at hPl
  generalize ((p - 1 : ℕ) : ℤ) = c at *
  generalize (Nat.log p (NN m) : ℤ) = Λ at *
  generalize ∑ z ∈ Zs m, (padicValInt p (zv k z) : ℤ) = ZS at *
  generalize (blocks.map (fun b => (b.2 : ℤ) *
          ∑ k' ∈ (blk m b).erase k, (padicValInt p ((k' : ℤ) - k) : ℤ))).sum = PS at *
  nlinarith

theorem Esmall_sub_le (m : ℕ) :
    ((p - 1 : ℕ) : ℚ) * ((Esmall m p : ℚ) - (G : ℚ) * (padicValNat p (nOf m).factorial : ℚ))
      ≤ 18 + 73 * ((p - 1 : ℕ) : ℚ) * ((Nat.log p (NN m) : ℚ) + 1) := by
  have hsup : ((p - 1 : ℕ) : ℤ) * (range (nOf m + 1)).sup' nonempty_range_add_one
      (fun k => -nuSmall m p k)
      ≤ 1094 * ((m : ℤ) + 1) + 18 + 46 * ((p - 1 : ℕ) : ℤ) * ((Nat.log p (NN m) : ℤ) + 1) := by
    obtain ⟨k, hk, hkeq⟩ := exists_mem_eq_sup' nonempty_range_add_one (fun k => -nuSmall m p k)
    rw [hkeq]
    exact neg_nuSmall_le m k (Nat.lt_succ_iff.mp (mem_range.mp hk))
  have hleg := legendre_lower (p := p) (nOf m)
  have hlogn : Nat.log p (nOf m) ≤ Nat.log p (NN m) := Nat.log_mono_right (nOf_lt_NN m).le
  have hEs : (Esmall m p : ℚ) = (((range (nOf m + 1)).sup' nonempty_range_add_one
      (fun k => -nuSmall m p k) : ℤ) : ℚ) + 22 * ((Nat.log p (NN m) : ℕ) : ℚ) := by
    unfold Esmall; push_cast; ring
  rw [hEs]
  have hn : nOf m = 240 * (m + 1) := rfl
  generalize padicValNat p (nOf m).factorial = V at *
  generalize (range (nOf m + 1)).sup' nonempty_range_add_one (fun k => -nuSmall m p k) = S at *
  generalize Nat.log p (nOf m) = Λn at *
  generalize Nat.log p (NN m) = Λ at *
  generalize p - 1 = c at *
  rw [hn] at hleg
  have hsupQ : (c : ℚ) * (S : ℚ) ≤ 1094 * ((m : ℚ) + 1) + 18 + 46 * (c : ℚ) * ((Λ : ℚ) + 1) := by
    exact_mod_cast hsup
  have hlegQ : 240 * ((m : ℚ) + 1) - (c : ℚ) * ((Λn : ℚ) + 1) ≤ (c : ℚ) * (V : ℚ) := by
    have h := (Int.cast_le (R := ℚ)).mpr hleg
    push_cast at h
    linarith
  have hlognQ : (Λn : ℚ) ≤ (Λ : ℚ) := by exact_mod_cast hlogn
  have hc0 : (0 : ℚ) ≤ (c : ℚ) := by positivity
  have hΛ0 : (0 : ℚ) ≤ (Λ : ℚ) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hlognQ hc0
  have h2 : (0 : ℚ) ≤ (c : ℚ) * (Λ : ℚ) := by positivity
  simp only [G]
  nlinarith

/-- Pointwise: `E_p - G v_p(n!) ≤ 91 (Λ_p + 1)` for `p² ≤ 𝒩`. -/
theorem Ep_sub_le_small (m : ℕ) (hN : p ^ 2 ≤ NN m) :
    (Ep m p : ℚ) - (G : ℚ) * (padicValNat p (nOf m).factorial : ℚ)
      ≤ 91 * ((Nat.log p (NN m) : ℚ) + 1) := by
  have hpn : ¬ nOf m < p := by
    intro h
    have h1 : nOf m * nOf m < p * p := Nat.mul_self_lt_mul_self h
    unfold nOf NN at *
    nlinarith
  have hE : Ep m p = Esmall m p := by
    simp [Ep, hpn, show ¬ NN m < p ^ 2 by omega]
  rw [hE]
  have h := Esmall_sub_le (p := p) m
  have hp2 : 2 ≤ p := hp.out.two_le
  have hc : (1 : ℚ) ≤ ((p - 1 : ℕ) : ℚ) := by
    have : 1 ≤ p - 1 := by omega
    exact_mod_cast this
  have hΛ : (0 : ℚ) ≤ (Nat.log p (NN m) : ℚ) := by positivity
  set X := (Esmall m p : ℚ) - (G : ℚ) * (padicValNat p (nOf m).factorial : ℚ)
  by_contra hcon
  push Not at hcon
  nlinarith

end Small

/-- **Size at the small primes.**
`Σ_{2 ≤ p ≤ √𝒩, p prime} (E_p - G v_p(n!)) log p ≤ 182 ⌊√𝒩⌋ log 𝒩`. -/
theorem small_primes_sum_le (m : ℕ) :
    ∑ p ∈ (Icc 2 (Nat.sqrt (NN m))).filter Nat.Prime,
        ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ)) * Real.log p
      ≤ 182 * (Nat.sqrt (NN m) : ℝ) * Real.log (NN m) := by
  have hNpos : (0 : ℝ) < NN m := by unfold NN; positivity
  have hterm : ∀ p ∈ (Icc 2 (Nat.sqrt (NN m))).filter Nat.Prime,
      ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ)) * Real.log p
        ≤ 182 * Real.log (NN m) := by
    intro p hp
    obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
    have hpI' := mem_Icc.mp hpI
    have : Fact p.Prime := ⟨hpP⟩
    have hpN : p ^ 2 ≤ NN m := Nat.le_sqrt'.mp hpI'.2
    have h := Ep_sub_le_small (p := p) m hpN
    have hR : ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ))
        ≤ 91 * ((Nat.log p (NN m) : ℝ) + 1) := by exact_mod_cast h
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    have hpNN : p ≤ NN m := le_trans (Nat.le_self_pow (by norm_num) p) hpN
    have hlogpN : Real.log p ≤ Real.log (NN m) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast hpNN)
    have hpow : p ^ Nat.log p (NN m) ≤ NN m := Nat.pow_log_le_self p (by unfold NN; omega)
    have hΛlog : (Nat.log p (NN m) : ℝ) * Real.log p ≤ Real.log (NN m) := by
      rw [← Real.log_pow]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
      exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    calc ((Ep m p : ℝ) - (G : ℝ) * (padicValNat p (nOf m).factorial : ℝ)) * Real.log p
        ≤ 91 * ((Nat.log p (NN m) : ℝ) + 1) * Real.log p :=
          mul_le_mul_of_nonneg_right hR hlogp
      _ = 91 * ((Nat.log p (NN m) : ℝ) * Real.log p + Real.log p) := by ring
      _ ≤ 91 * (Real.log (NN m) + Real.log (NN m)) := by gcongr
      _ = 182 * Real.log (NN m) := by ring
  have hcard : (#((Icc 2 (Nat.sqrt (NN m))).filter Nat.Prime) : ℝ) ≤ Nat.sqrt (NN m) := by
    have h1 := card_filter_le (Icc 2 (Nat.sqrt (NN m))) Nat.Prime
    rw [Nat.card_Icc] at h1
    exact_mod_cast h1.trans (by omega)
  have hlogN : 0 ≤ Real.log (NN m) := Real.log_nonneg (by unfold NN; norm_cast; omega)
  calc _ ≤ ∑ p ∈ (Icc 2 (Nat.sqrt (NN m))).filter Nat.Prime, 182 * Real.log (NN m) :=
        sum_le_sum hterm
    _ = (#((Icc 2 (Nat.sqrt (NN m))).filter Nat.Prime) : ℝ) * (182 * Real.log (NN m)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (Nat.sqrt (NN m) : ℝ) * (182 * Real.log (NN m)) := by gcongr
    _ = 182 * (Nat.sqrt (NN m) : ℝ) * Real.log (NN m) := by ring

end ZetaIrr.Z7.Arith
