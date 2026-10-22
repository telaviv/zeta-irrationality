/-
# Glue (Z7): Lemma 5 reduction (PNT step) — the sharp-sum bound from pointwise + step data

`sharp_of_pointwise` derives the Lemma 5 bound (the bound
`Σ_{√𝒩 < p ≤ n} (E_p - G⌊n/p⌋) log p ≤ n (A + o(1))`) from
* (a) a pointwise bound `E_p - G⌊n/p⌋ ≤ e*(n/p)` for primes `√𝒩 < p ≤ n` (`estar : ℚ → ℝ`);
* (b) step data `x 0 = 1 < x 1 < … < x L = X`, `e* ≤ u i` at rational points of each open cell,
  and the tail bound `e*(y) ≤ C + G {y}` for rational `y ≥ X` (`C ≥ 0`);
* (c) `Σ_i u_i (1/x_i − 1/x_{i+1}) + C/X + G/(2(X−1)) ≤ A`.

**How the omitted primes are handled.** The PNT package `eventually_primeSum_lemma5_le` bounds the
sum over *all* primes `p ≤ n/x 0 = n` of `h(n/p) log p`. We apply it to
`h' y = e*(y)` for `y < X` and `h' y = max(e*(y), 0)` for `y ≥ X`
(the tail majorant `C + G{y} ≥ 0` still dominates `h'`, as `C, G ≥ 0`). For large `n`, every prime `p ≤ n` that is not
in the sharp range has `p² ≤ 𝒩`, hence `n/p ≥ X` and `h'(n/p) ≥ 0`; so dropping those primes only
decreases the sum. On the sharp primes, `E_p - G⌊n/p⌋ ≤ e*(n/p) ≤ h'(n/p)`. No lower bound on
`e*` is needed. (Irrational `y` never occur as `n/p`; there `h'` is set to a value below every `u i`.)

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Glue.Errors
import ZetaIrrational.PNT.PrimeSums

namespace ZetaIrr.Z7

open Filter Topology Finset ZetaIrr.PNT

/-- The sharp sum `Σ_{p prime, p ≤ n, 𝒩 < p²} (E_p - G⌊n/p⌋) log p` of `log_D_sub_le`. -/
noncomputable def sharpSum (m : ℕ) : ℝ :=
  ∑ p ∈ Arith.sharpPrimes m,
    ((Arith.Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ)) * Real.log p

/-- From `∀ ε > 0, eventually F ≤ a (A + ε)` to an explicit `εS → 0`. -/
lemma exists_eps_of_forall {F a : ℕ → ℝ} (ha : ∀ m, 0 < a m) {A : ℝ}
    (h : ∀ ε > 0, ∀ᶠ m in atTop, F m ≤ a m * A + ε * a m) :
    ∃ εS : ℕ → ℝ, Tendsto εS atTop (𝓝 0) ∧ ∀ m, F m ≤ a m * (A + εS m) := by
  refine ⟨fun m => max (F m / a m - A) 0, ?_, fun m => ?_⟩
  · rw [tendsto_order]
    refine ⟨fun b hb => Eventually.of_forall (fun m => hb.trans_le (le_max_right _ _)),
      fun b hb => ?_⟩
    filter_upwards [h (b / 2) (half_pos hb)] with m hm
    refine max_lt ?_ hb
    have ham := ha m
    have : F m / a m ≤ A + b / 2 := by
      rw [div_le_iff₀ ham]; linarith
    linarith
  · have ham := ha m
    have h1 : F m / a m - A ≤ max (F m / a m - A) 0 := le_max_left _ _
    have h2 : F m / a m ≤ A + max (F m / a m - A) 0 := by linarith
    rwa [div_le_iff₀ ham, mul_comm] at h2

lemma chain_le {x : ℕ → ℝ} {L : ℕ} (hx : ∀ i < L, x i < x (i + 1)) :
    ∀ k i, i + k ≤ L → x i ≤ x (i + k)
  | 0, _, _ => le_rfl
  | k + 1, i, h => (chain_le hx k i (by omega)).trans
      (by rw [← add_assoc]; exact (hx (i + k) (by omega)).le)

lemma tendsto_nOf_nat : Tendsto nOf atTop atTop :=
  tendsto_atTop_mono (fun m => show m ≤ nOf m by unfold nOf; omega) tendsto_id

/-- For `m + 1 ≥ X²`: a prime `p` with `p² ≤ 𝒩` has `X p ≤ n`. -/
lemma mul_le_nOf_of_sq_le (X m p : ℕ) (hm : X ^ 2 ≤ m + 1) (hp : p ^ 2 ≤ Arith.NN m) :
    X * p ≤ nOf m := by
  have h1 : (X * p) ^ 2 ≤ nOf m ^ 2 := by
    unfold Arith.NN at hp; unfold nOf
    have : (X * p) ^ 2 = X ^ 2 * p ^ 2 := by ring
    rw [this]
    calc X ^ 2 * p ^ 2 ≤ X ^ 2 * (700 * (m + 1) + 1) := Nat.mul_le_mul_left _ hp
      _ ≤ (m + 1) * (700 * (m + 1) + 1) := Nat.mul_le_mul_right _ hm
      _ ≤ (240 * (m + 1)) ^ 2 := by nlinarith
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1

/-- **Lemma 5 reduction (PNT step), ε-form.** -/
theorem sharp_le_of_pointwise (estar : ℚ → ℝ)
    (hpt : ∀ᶠ m in atTop, ∀ p : ℕ, p.Prime → p ≤ nOf m → Arith.NN m < p ^ 2 →
      (Arith.Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ) ≤ estar ((nOf m : ℚ) / p))
    (x u : ℕ → ℝ) (L X : ℕ) (hX : 2 ≤ X) (hx0 : x 0 = 1) (hx : ∀ i < L, x i < x (i + 1))
    (hxL : x L = X)
    (hcell : ∀ i < L, ∀ q : ℚ, x i < q → (q : ℝ) < x (i + 1) → estar q ≤ u i)
    (C : ℝ) (hC : 0 ≤ C)
    (htail : ∀ q : ℚ, (X : ℚ) ≤ q → estar q ≤ C + (G : ℝ) * ((Int.fract q : ℚ) : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, sharpSum m ≤
      (nOf m : ℝ) * (∑ i ∈ range L, u i * (1 / x i - 1 / x (i + 1)) + C / X +
        (G : ℝ) / (2 * ((X : ℝ) - 1))) + ε * nOf m := by
  classical
  set K : ℝ := ∑ i ∈ range L, |u i| with hK
  have hK0 : 0 ≤ K := sum_nonneg (fun i _ => abs_nonneg _)
  -- the real-variable weight
  let h0 : ℝ → ℝ := fun y => if hy : ∃ q : ℚ, (q : ℝ) = y then estar hy.choose else -K
  let h' : ℝ → ℝ := fun y => if (X : ℝ) ≤ y then max (h0 y) 0 else h0 y
  have h0q : ∀ q : ℚ, h0 q = estar q := by
    intro q
    have hy : ∃ q' : ℚ, (q' : ℝ) = q := ⟨q, rfl⟩
    simp only [h0, dif_pos hy]
    congr 1
    exact_mod_cast hy.choose_spec
  have h0irr : ∀ y : ℝ, (¬ ∃ q : ℚ, (q : ℝ) = y) → h0 y = -K := by
    intro y hy; simp only [h0, dif_neg hy]
  have h0le : ∀ y, h0 y ≤ h' y := by
    intro y; simp only [h']; split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hG : (0 : ℝ) ≤ G := by exact_mod_cast H1.le
  have hX' : (2 : ℝ) ≤ X := by exact_mod_cast hX
  -- package hypotheses
  have hx0' : 0 < x 0 := by rw [hx0]; norm_num
  have hcell' : ∀ i < L, ∀ y, x i < y → y < x (i + 1) → h' y ≤ u i := by
    intro i hi y h1 h2
    have hyX : ¬ (X : ℝ) ≤ y := by
      have := chain_le hx (L - (i + 1)) (i + 1) (by omega)
      rw [show i + 1 + (L - (i + 1)) = L by omega, hxL] at this
      linarith
    simp only [h', if_neg hyX]
    by_cases hq : ∃ q : ℚ, (q : ℝ) = y
    · obtain ⟨q, rfl⟩ := hq
      rw [h0q]
      exact hcell i hi q h1 h2
    · rw [h0irr y hq]
      have : |u i| ≤ K := single_le_sum (f := fun i => |u i|) (fun _ _ => abs_nonneg _)
        (mem_range.mpr hi)
      linarith [neg_abs_le (u i)]
  have htail' : ∀ y, (X : ℝ) ≤ y → h' y ≤ C + (G : ℝ) * Int.fract y := by
    intro y hy
    have hpos : 0 ≤ C + (G : ℝ) * Int.fract y := add_nonneg hC (mul_nonneg hG (Int.fract_nonneg _))
    simp only [h', if_pos hy]
    refine max_le ?_ hpos
    by_cases hq : ∃ q : ℚ, (q : ℝ) = y
    · obtain ⟨q, rfl⟩ := hq
      rw [h0q, ← Rat.cast_fract]
      exact htail q (by exact_mod_cast hy)
    · rw [h0irr y hq]; linarith
  have hpkg := eventually_primeSum_lemma5_le h' x u L hx0' hx hcell' C (G : ℝ) hC hG X hX hxL
    htail' hε
  -- transfer to `m`
  filter_upwards [tendsto_nOf_nat.eventually hpkg, hpt, eventually_ge_atTop (X ^ 2)]
    with m hm hptm hmX
  rw [hx0, div_one] at hm
  set n := nOf m with hn
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  -- the sum over all primes `p ≤ n`
  set Sall := (Arith.primesD m).filter
    (fun p : ℕ => p.Prime ∧ (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) ≤ (n : ℝ)) with hSall
  have hps : primeSum (fun p => h' ((n : ℝ) / p)) 0 n =
      ∑ p ∈ Sall, h' ((n : ℝ) / p) * Real.log p := by
    refine primeSum_eq_sum_filter _ hn0 _ (fun p hp _ hpn => ?_)
    simp only [Arith.primesD, mem_filter, mem_range]
    refine ⟨?_, hp⟩
    have : p ≤ n := by exact_mod_cast hpn
    omega
  rw [hps] at hm
  set Ssh := Arith.sharpPrimes m with hSsh
  have hsub : Ssh ⊆ Sall := by
    intro p hp
    simp only [hSsh, hSall, Arith.sharpPrimes, Arith.primesD, mem_filter, mem_range] at hp ⊢
    refine ⟨hp.1, hp.1.2, by exact_mod_cast hp.1.2.pos, by exact_mod_cast (show p ≤ nOf m by omega)⟩
  have step1 : sharpSum m ≤ ∑ p ∈ Ssh, h' ((n : ℝ) / p) * Real.log p := by
    unfold sharpSum
    refine sum_le_sum (fun p hp => ?_)
    simp only [Arith.sharpPrimes, Arith.primesD, mem_filter, mem_range] at hp
    refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
    have h1 := hptm p hp.1.2 (by omega) hp.2
    have e : ((((nOf m : ℚ) / p : ℚ)) : ℝ) = (n : ℝ) / p := by push_cast; rfl
    calc (Arith.Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ)
        ≤ estar ((nOf m : ℚ) / p) := h1
      _ = h0 ((n : ℝ) / p) := by rw [← e, h0q]
      _ ≤ h' ((n : ℝ) / p) := h0le _
  have step2 : ∑ p ∈ Ssh, h' ((n : ℝ) / p) * Real.log p ≤
      ∑ p ∈ Sall, h' ((n : ℝ) / p) * Real.log p := by
    refine sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot => ?_)
    simp only [hSsh, hSall, Arith.sharpPrimes, Arith.primesD, mem_filter, mem_range, not_and,
      not_lt] at hp hnot
    have hpn : p ≤ n := by exact_mod_cast hp.2.2.2
    have hsq := hnot hp.1
    have hXp := mul_le_nOf_of_sq_le X m p (by omega) hsq
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
    have hy : (X : ℝ) ≤ (n : ℝ) / p := by
      rw [le_div_iff₀ hp0]; exact_mod_cast hXp
    refine mul_nonneg ?_ (Real.log_natCast_nonneg p)
    simp only [h', if_pos hy]
    exact le_max_right _ _
  linarith

/-- **Lemma 5 reduction (PNT step)**, with `X = 400` style data. -/
theorem sharp_of_pointwise (estar : ℚ → ℝ)
    (hpt : ∀ᶠ m in atTop, ∀ p : ℕ, p.Prime → p ≤ nOf m → Arith.NN m < p ^ 2 →
      (Arith.Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ) ≤ estar ((nOf m : ℚ) / p))
    (x u : ℕ → ℝ) (L X : ℕ) (hX : 2 ≤ X) (hx0 : x 0 = 1) (hx : ∀ i < L, x i < x (i + 1))
    (hxL : x L = X)
    (hcell : ∀ i < L, ∀ q : ℚ, x i < q → (q : ℝ) < x (i + 1) → estar q ≤ u i)
    (C : ℝ) (hC : 0 ≤ C)
    (htail : ∀ q : ℚ, (X : ℚ) ≤ q → estar q ≤ C + (G : ℝ) * ((Int.fract q : ℚ) : ℝ))
    (A : ℝ)
    (hcert : ∑ i ∈ range L, u i * (1 / x i - 1 / x (i + 1)) + C / X +
        (G : ℝ) / (2 * ((X : ℝ) - 1)) ≤ A) :
    ∃ εS : ℕ → ℝ, Tendsto εS atTop (𝓝 0) ∧
      ∀ᶠ m in atTop,
        ∑ p ∈ Arith.sharpPrimes m,
            ((Arith.Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ)) * Real.log p
          ≤ (nOf m : ℝ) * (A + εS m) := by
  obtain ⟨εS, hlim, hle⟩ := exists_eps_of_forall (F := sharpSum) (a := fun m => (nOf m : ℝ))
    nOf_pos (A := A) (fun ε hε => by
      filter_upwards [sharp_le_of_pointwise estar hpt x u L X hX hx0 hx hxL hcell C hC htail hε]
        with m hm
      have := nOf_pos m
      nlinarith)
  exact ⟨εS, hlim, Eventually.of_forall hle⟩

end ZetaIrr.Z7
