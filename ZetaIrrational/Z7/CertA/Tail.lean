/-
# The uniform tail bound for `e*` (Lemma 5) for instance Z7

For `x ≥ 1`: `e*(x) ≤ 32 + G{x} ≤ 33 + G{x}` (`eStar_le_tail`), with `E_tail = S + 15 = 33` the
constant used in `CertA.tail`.

Proof (at real `x, y`): per block `j`, `[in block] + P_j ≤ 1 + (1 - 2δ_j) x`
(in block: `⌊y-δx⌋ + ⌊(1-δ)x-y⌋ ≤ (1-2δ)x`; out of block: `⌊a⌋ - ⌊b⌋ + [b ∈ ℤ] ≤ a - b + 1`);
each zero run has `≥ rx - 1` hits, so `c ≥ 10rx - 10`; and `Σ_j m_j (1 - 2δ_j) = G + 10r`,
`Σ_j m_j = 18`. Hence every bracket value is `≤ max(0, 18 + 4 + 10 + Gx) = 32 + Gx`.
-/
import ZetaIrrational.Z7.CertA.Attain

namespace ZetaIrr.Z7.CertA

/-- `⌊a⌋ - ⌊b⌋ + [b ∈ ℤ] ≤ a - b + 1`. -/
lemma floor_sub_floor_ind_le (a b : ℚ) :
    ((⌊a⌋ - ⌊b⌋ + (if Int.fract b = 0 then 1 else 0) : ℤ) : ℚ) ≤ a - b + 1 := by
  have ha := Int.floor_le a
  have hb := Int.sub_one_lt_floor b
  split_ifs with h
  · have hb' : (⌊b⌋ : ℚ) = b := by
      have := Int.self_sub_floor b
      rw [Int.fract] at h
      linarith
    push_cast; linarith
  · push_cast; linarith

/-- One block: `[in block] + P_j ≤ 1 + (1 - 2δ_j) x`. -/
lemma ind_add_Pfun_le (d : ℕ) (x y : ℚ) :
    (((if dlt d * x ≤ y ∧ y ≤ (1 - dlt d) * x then 1 else 0 : ℤ) + Pfun d x y : ℤ) : ℚ)
      ≤ 1 + (1 - 2 * dlt d) * x := by
  unfold Pfun
  by_cases hin : dlt d * x ≤ y ∧ y ≤ (1 - dlt d) * x
  · rw [if_pos hin, if_pos hin]
    have h1 := Int.floor_le (y - dlt d * x)
    have h2 := Int.floor_le ((1 - dlt d) * x - y)
    push_cast; linarith
  · rw [if_neg hin, if_neg hin, zero_add]
    by_cases hlt : y < dlt d * x
    · rw [if_pos hlt]
      have := floor_sub_floor_ind_le ((1 - dlt d) * x - y) (dlt d * x - y)
      have e : (1 - dlt d) * x - y - (dlt d * x - y) + 1 = 1 + (1 - 2 * dlt d) * x := by ring
      rwa [e] at this
    · rw [if_neg hlt]
      have := floor_sub_floor_ind_le (y - dlt d * x) (y - (1 - dlt d) * x)
      have e : y - dlt d * x - (y - (1 - dlt d) * x) + 1 = 1 + (1 - 2 * dlt d) * x := by ring
      rwa [e] at this

/-- The zero runs: `c(y) ≥ 10 r x - 10`. -/
lemma cfun_ge (x y : ℚ) : 110 / 12 * x - 10 ≤ (cfun x y : ℚ) := by
  unfold cfun rr
  have h1 := Int.lt_floor_add_one (y + 11 / 12 * x)
  have h2 := Int.floor_le y
  have h3 := Int.le_ceil (y - x)
  have h4 := Int.ceil_lt_add_one (y - (1 + 11 / 12) * x)
  push_cast
  linarith

/-- The per-block bounds, summed over any list of blocks. -/
lemma blocks_sum_le (x y : ℚ) (l : List (ℕ × ℕ)) :
    ((((l.map fun b =>
        ((if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then b.2 else 0 : ℕ) : ℤ)).sum : ℤ) : ℚ)
      + (((l.map fun b => (b.2 : ℤ) * Pfun b.1 x y).sum : ℤ) : ℚ))
      ≤ (l.map fun b => (b.2 : ℚ) * (1 + (1 - 2 * dlt b.1) * x)).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hb := ind_add_Pfun_le b.1 x y
    have hmm : (0 : ℚ) ≤ b.2 := by positivity
    have e : ((((if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then b.2 else 0 : ℕ) : ℤ)
        + (b.2 : ℤ) * Pfun b.1 x y : ℤ) : ℚ) =
        (b.2 : ℚ) * (((if dlt b.1 * x ≤ y ∧ y ≤ (1 - dlt b.1) * x then 1 else 0 : ℤ)
          + Pfun b.1 x y : ℤ) : ℚ) := by
      split_ifs <;> push_cast <;> ring
    have h1 := mul_le_mul_of_nonneg_left hb hmm
    rw [← e] at h1
    push_cast at h1 ih ⊢
    linarith

/-- `Σ_j m_j (1 + (1 - 2δ_j) x) = 18 + (G + 10 r) x = 18 + (1647/120) x` for the Z7 blocks. -/
lemma blocks_weight (x : ℚ) :
    (blocks.map fun b => (b.2 : ℚ) * (1 + (1 - 2 * dlt b.1) * x)).sum = 18 + 1647 / 120 * x := by
  simp only [blocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dlt]
  push_cast
  ring

/-- **Uniform bound for Z7.** `gfun(x, y) ≤ 32 + Gx` for `x ≥ 1`. -/
theorem gfun_le_tail (x y : ℚ) (hx : 1 ≤ x) : (gfun x y : ℚ) ≤ 32 + G * x := by
  have hc := cfun_ge x y
  have hsum := blocks_sum_le x y blocks
  rw [blocks_weight] at hsum
  have h3 : ((Sfun x y : ℤ) : ℚ) + ((Ptot x y : ℤ) : ℚ) ≤ 18 + 1647 / 120 * x := by
    rw [Sfun_cast]; exact hsum
  have hG : G = 547 / 120 := rfl
  have hmain : ((Sfun x y : ℤ) : ℚ) + 4 - (cfun x y : ℚ) + (Ptot x y : ℚ) ≤ 32 + G * x := by
    rw [hG]; linarith
  have hGx : (0 : ℚ) ≤ 32 + G * x := by
    have : (0 : ℚ) < G := by norm_num [G]
    nlinarith
  unfold gfun bracket
  split_ifs <;> push_cast at hmain ⊢ <;> linarith

/-- **Tail bound for `e*`.** For `x ≥ 1`: `e*(x) ≤ 33 + G{x}`. -/
theorem eStar_le_tail (x : ℚ) (hx : 1 ≤ x) : eStar x ≤ 33 + G * Int.fract x := by
  obtain ⟨⟨y, -, -, hy⟩, -⟩ := eStar_isGreatest x hx
  rw [← hy]
  have h := gfun_le_tail x y hx
  have hfr : (⌊x⌋ : ℚ) = x - Int.fract x := by rw [Int.fract]; ring
  rw [hfr]
  nlinarith

end ZetaIrr.Z7.CertA
