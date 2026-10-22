/-
# Lemma 5 (pointwise part) for instance Z7

The counts `c_p(k)`, `P_{p,j}(k)` of Lemma A, the per-`k` exponent `e_p(k)` of Lemma 4, and the
pointwise bound of Lemma 5.

For `n = nOf m = 240(m+1)`, every `0 < p ≤ n` (in particular every prime `√𝒩 < p ≤ n`) and every
`k` with `B_k ≥ 1`:

  `e_p(k) - G ⌊n/p⌋ ≤ e*(n/p)`  (`pointwise_le_eStar`),

where `e_p(k) = epk m p k` is the per-`k` exponent of Lemma 4 with the counts below:
* `B_k + 4 - c_p(k) + P_p(k)` if `k ≥ p`;
* `B_k - 1 - c_p(k) + P_p(k)` if `k < p` and `P_p(k) ≥ 1`;
* `0` if `k < p` and `P_p(k) = 0`;

with
* `c_p(k) = 5 · #{l ∈ [1, rn] : p ∣ k + l} + 5 · #{l ∈ [n+1, (1+r)n] : p ∣ l - k}` (the zeros
  `t = l` and `t = -l` of multiplicity 5, at distance `-(k+l)` resp. `l - k` from the pole `-k`;
  the `e`-term `[p ∣ n - 2k]` is omitted, it only increases `c_p(k)` and so decreases `e_p(k)`),
* `P_p(k) = Σ_j m_j P_{p,j}(k)`, `P_{p,j}(k) = #{k' ∈ [a_j, b_j], k' ≠ k : p ∣ k' - k}`,
  `a_j = 3 d_j (m+1) = δ_j n`, `b_j = n - a_j`.

Proof: `B_k = S(k/p)`, `P_{p,j}(k) = P_j(k/p)` (`Pfun_eq_Ppj`) and `c_p(k) = c(k/p)` (`cfun_eq_cp`)
exactly, and `k ≥ p ⟺ k/p ≥ 1`, so `e_p(k) = bracket(n/p, k/p) ≤ eStarInt(n/p)`
(`bracket_le_eStarInt`).
-/
import ZetaIrrational.Z7.CertA.Sound
import ZetaIrrational.Z7.Concrete.Data

namespace ZetaIrr.Z7.CertA

open Finset

/-! ## Definitions (Lemma A, Lemma 4) -/

/-- `c_p(k)`: zeros `l ∈ [1, rn]` (distance `-(k+l)`) and `-l`, `l ∈ [n+1, (1+r)n]` (distance
`l - k`), multiplicity 5; `rn = 220(m+1)`, `(1+r)n = 460(m+1)`. -/
def cp (m p k : ℕ) : ℕ :=
  5 * #{l ∈ Icc (1 : ℤ) (220 * ((m : ℤ) + 1)) | (p : ℤ) ∣ (k : ℤ) + l} +
    5 * #{l ∈ Icc ((nOf m : ℤ) + 1) (460 * ((m : ℤ) + 1)) | (p : ℤ) ∣ l - k}

/-- `P_{p,j}(k) = #{k' ∈ [a_j, b_j], k' ≠ k : p ∣ k' - k}` for the block with `δ_j = d/80`. -/
def Ppj (m p d k : ℕ) : ℕ :=
  #{k' ∈ (Icc ((3 * d * (m + 1) : ℕ) : ℤ) ((nOf m - 3 * d * (m + 1) : ℕ) : ℤ)).erase (k : ℤ) |
    (p : ℤ) ∣ k' - k}

/-- `P_p(k) = Σ_j m_j P_{p,j}(k)`. -/
def Pp (m p k : ℕ) : ℤ := (blocks.map fun b => (b.2 : ℤ) * (Ppj m p b.1 k : ℤ)).sum

/-- The per-`k` exponent `e_p(k)` of Lemma 4 (with `c_p` without the `e`-term). -/
def epk (m p k : ℕ) : ℤ :=
  if p ≤ k then (Bk m k : ℤ) + 4 - cp m p k + Pp m p k
  else if 1 ≤ Pp m p k then (Bk m k : ℤ) - 1 - cp m p k + Pp m p k
  else 0

/-! ## Floors of `N/p` -/

/-- `⌊N/p⌋` as a rational floor. -/
def flp (p : ℕ) (N : ℤ) : ℤ := ⌊(N : ℚ) / ((p : ℤ) : ℚ)⌋

section flp
variable {p : ℕ} (hp : 0 < p)
include hp

lemma flp_bounds (N : ℤ) : flp p N * p ≤ N ∧ N < (flp p N + 1) * p := by
  have hp' : (0 : ℚ) < ((p : ℤ) : ℚ) := by exact_mod_cast hp
  have h1 := Int.floor_le ((N : ℚ) / ((p : ℤ) : ℚ))
  have h2 := Int.lt_floor_add_one ((N : ℚ) / ((p : ℤ) : ℚ))
  rw [le_div_iff₀ hp'] at h1
  rw [div_lt_iff₀ hp'] at h2
  unfold flp
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

lemma flp_eq (N a : ℤ) (h1 : a * p ≤ N) (h2 : N < (a + 1) * p) : flp p N = a :=
  floor_div_eq N p a (by exact_mod_cast hp) h1 h2

lemma flp_neg_succ (N : ℤ) : flp p (-N - 1) = -flp p N - 1 := by
  obtain ⟨h1, h2⟩ := flp_bounds hp N
  apply flp_eq hp <;> nlinarith

lemma flp_neg (N : ℤ) : flp p (-N) = -flp p N - (if (p : ℤ) ∣ N then 0 else 1) := by
  obtain ⟨h1, h2⟩ := flp_bounds hp N
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    have hc : flp p (p * c) = c := flp_eq hp _ _ (by nlinarith) (by nlinarith)
    rw [hc]
    apply flp_eq hp <;> nlinarith
  · have hne : flp p N * p ≠ N := fun h => hd (Dvd.intro_left _ h)
    have hlt : flp p N * p < N := lt_of_le_of_ne h1 hne
    apply flp_eq hp <;> nlinarith

lemma flp_pred (N : ℤ) : flp p (N - 1) = flp p N - (if (p : ℤ) ∣ N then 1 else 0) := by
  obtain ⟨h1, h2⟩ := flp_bounds hp N
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    have hc : flp p (p * c) = c := flp_eq hp _ _ (by nlinarith) (by nlinarith)
    rw [hc]
    apply flp_eq hp <;> nlinarith
  · have hne : flp p N * p ≠ N := fun h => hd (Dvd.intro_left _ h)
    have hlt : flp p N * p < N := lt_of_le_of_ne h1 hne
    apply flp_eq hp <;> nlinarith

lemma fract_div_eq_zero (N : ℤ) : Int.fract ((N : ℚ) / ((p : ℤ) : ℚ)) = 0 ↔ (p : ℤ) ∣ N := by
  have hp' : ((p : ℤ) : ℚ) ≠ 0 := by
    have : (0 : ℚ) < ((p : ℤ) : ℚ) := by exact_mod_cast hp
    exact this.ne'
  rw [Int.fract_eq_zero_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : (N : ℚ) = (p : ℤ) * z := by rw [hz]; field_simp
    exact_mod_cast this
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    push_cast
    field_simp

/-- Multiples of `p` among `k' - c`, `k' ∈ [a, b]`. -/
lemma card_Icc_dvd (a b c : ℤ) (hab : a ≤ b) :
    (#{k' ∈ Icc a b | (p : ℤ) ∣ k' - c} : ℤ) = flp p (b - c) - flp p (a - 1 - c) := by
  have hbij : #{k' ∈ Icc a b | (p : ℤ) ∣ k' - c} = #{t ∈ Ioc (a - 1 - c) (b - c) | (p : ℤ) ∣ t} := by
    apply Finset.card_nbij' (fun k' => k' - c) (fun t => t + c)
    · intro k' hk'
      simp only [coe_filter, Set.mem_setOf_eq, mem_Icc, mem_Ioc] at hk' ⊢
      exact ⟨⟨by omega, by omega⟩, hk'.2⟩
    · intro t ht
      simp only [coe_filter, Set.mem_setOf_eq, mem_Icc, mem_Ioc] at ht ⊢
      exact ⟨⟨by omega, by omega⟩, by simpa using ht.2⟩
    · intro k' _; simp
    · intro t _; simp
  rw [hbij, Int.Ioc_filter_dvd_card _ _ (by exact_mod_cast hp : (0 : ℤ) < p)]
  have hmono : flp p (a - 1 - c) ≤ flp p (b - c) := by
    unfold flp
    apply Int.floor_le_floor
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (by omega : a - 1 - c ≤ b - c)
  unfold flp at hmono ⊢
  push_cast at hmono ⊢
  omega

/-- `P_{p,j}(k)` in closed form. -/
lemma card_block (A B k : ℤ) (hAB : A ≤ B) :
    (#{k' ∈ (Icc A B).erase k | (p : ℤ) ∣ k' - k} : ℤ) =
      flp p (B - k) - flp p (A - 1 - k) - (if A ≤ k ∧ k ≤ B then 1 else 0) := by
  rw [Finset.filter_erase]
  split_ifs with hk
  · rw [Finset.card_erase_of_mem (by simp [hk])]
    have hpos : 0 < #{k' ∈ Icc A B | (p : ℤ) ∣ k' - k} :=
      Finset.card_pos.2 ⟨k, by simp [hk]⟩
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hpos.ne')]
    rw [card_Icc_dvd hp A B k hAB]
  · rw [Finset.erase_eq_of_notMem (by simp; omega), card_Icc_dvd hp A B k hAB]
    ring

/-- The Lemma 5 formula for `P_j` at `x = n/p`, `y = k/p` equals the count `P_{p,j}(k)`. -/
lemma Pgen_eq (A B k : ℕ) (hAB : A ≤ B) :
    (if (A : ℚ) / p ≤ (k : ℚ) / p ∧ (k : ℚ) / p ≤ (B : ℚ) / p then
        ⌊(k : ℚ) / p - (A : ℚ) / p⌋ + ⌊(B : ℚ) / p - (k : ℚ) / p⌋
      else if (k : ℚ) / p < (A : ℚ) / p then
        ⌊(B : ℚ) / p - (k : ℚ) / p⌋ - ⌊(A : ℚ) / p - (k : ℚ) / p⌋ +
          (if Int.fract ((A : ℚ) / p - (k : ℚ) / p) = 0 then 1 else 0)
      else
        ⌊(k : ℚ) / p - (A : ℚ) / p⌋ - ⌊(k : ℚ) / p - (B : ℚ) / p⌋ +
          (if Int.fract ((k : ℚ) / p - (B : ℚ) / p) = 0 then 1 else 0)) =
      (#{k' ∈ (Icc (A : ℤ) (B : ℤ)).erase (k : ℤ) | (p : ℤ) ∣ k' - k} : ℤ) := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hsub : ∀ a b : ℕ, (a : ℚ) / p - (b : ℚ) / p = (((a : ℤ) - b : ℤ) : ℚ) / ((p : ℤ) : ℚ) := by
    intro a b; push_cast; ring
  have hle : ∀ a b : ℕ, (a : ℚ) / p ≤ (b : ℚ) / p ↔ a ≤ b := by
    intro a b; rw [div_le_div_iff_of_pos_right hp']; exact Nat.cast_le
  have hlt : ∀ a b : ℕ, (a : ℚ) / p < (b : ℚ) / p ↔ a < b := by
    intro a b; rw [div_lt_div_iff_of_pos_right hp']; exact Nat.cast_lt
  rw [card_block hp A B k (by exact_mod_cast hAB)]
  have hf : ∀ N : ℤ, ⌊(N : ℚ) / ((p : ℤ) : ℚ)⌋ = flp p N := fun _ => rfl
  simp only [hsub, hle, hlt, fract_div_eq_zero hp, hf]
  have e1 : flp p ((A : ℤ) - 1 - k) = -flp p ((k : ℤ) - A) - 1 := by
    rw [show (A : ℤ) - 1 - k = -((k : ℤ) - A) - 1 by ring]; exact flp_neg_succ hp _
  have e2 : flp p ((A : ℤ) - 1 - k) =
      flp p ((A : ℤ) - k) - (if (p : ℤ) ∣ (A : ℤ) - k then 1 else 0) := by
    rw [show (A : ℤ) - 1 - k = ((A : ℤ) - k) - 1 by ring]; exact flp_pred hp _
  have e3 : flp p ((B : ℤ) - k) =
      -flp p ((k : ℤ) - B) - (if (p : ℤ) ∣ (k : ℤ) - B then 0 else 1) := by
    rw [show (B : ℤ) - k = -((k : ℤ) - B) by ring]; exact flp_neg hp _
  by_cases hin : A ≤ k ∧ k ≤ B
  · have hin' : (A : ℤ) ≤ k ∧ (k : ℤ) ≤ B := by omega
    rw [if_pos hin, if_pos hin', e1]; ring
  · have hin' : ¬((A : ℤ) ≤ k ∧ (k : ℤ) ≤ B) := by omega
    rw [if_neg hin, if_neg hin']
    by_cases hkA : k < A
    · rw [if_pos hkA, e2]; ring
    · rw [if_neg hkA, e1, e3]; split_ifs <;> ring

end flp

/-! ## The three ingredients at `x = n/p`, `y = k/p` -/

lemma blocks_d_le : ∀ b ∈ blocks, b.1 ≤ 18 := by decide

lemma dlt_mul_x (m p d : ℕ) :
    dlt d * ((nOf m : ℚ) / p) = ((3 * d * (m + 1) : ℕ) : ℚ) / p := by
  unfold dlt nOf; push_cast; ring

lemma one_sub_dlt_mul_x (m p d : ℕ) (hd : d ≤ 80) :
    (1 - dlt d) * ((nOf m : ℚ) / p) = ((nOf m - 3 * d * (m + 1) : ℕ) : ℚ) / p := by
  have h : 3 * d * (m + 1) ≤ nOf m := by unfold nOf; nlinarith
  rw [Nat.cast_sub h]
  unfold dlt nOf; push_cast; ring

/-- `B_k = S(k/p)` exactly. -/
lemma Sfun_eq_Bk (m p k : ℕ) (hp : 0 < p) : Sfun ((nOf m : ℚ) / p) ((k : ℚ) / p) = Bk m k := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hle : ∀ a b : ℕ, (a : ℚ) / p ≤ (b : ℚ) / p ↔ a ≤ b := by
    intro a b; rw [div_le_div_iff_of_pos_right hp']; exact Nat.cast_le
  unfold Sfun Bk
  congr 1
  apply List.map_congr_left
  intro b hb
  rw [dlt_mul_x, one_sub_dlt_mul_x m p b.1 (by have := blocks_d_le b hb; omega)]
  simp only [hle]

/-- `P_{p,j}(k) = P_j(k/p)` exactly (including the out-of-block indicator terms). -/
lemma Pfun_eq_Ppj (m p d k : ℕ) (hp : 0 < p) (hd : d ≤ 18) :
    Pfun d ((nOf m : ℚ) / p) ((k : ℚ) / p) = Ppj m p d k := by
  unfold Pfun Ppj
  rw [dlt_mul_x, one_sub_dlt_mul_x m p d (by omega)]
  have h1 : 3 * d * (m + 1) ≤ 54 * (m + 1) := Nat.mul_le_mul_right _ (by omega)
  exact Pgen_eq hp _ _ _ (by unfold nOf; omega)

lemma Ptot_eq_Pp (m p k : ℕ) (hp : 0 < p) :
    Ptot ((nOf m : ℚ) / p) ((k : ℚ) / p) = Pp m p k := by
  unfold Ptot Pp
  congr 1
  exact List.map_congr_left (fun b hb => by rw [Pfun_eq_Ppj m p b.1 k hp (blocks_d_le b hb)])

/-- `c(k/p) = c_p(k)`: the hits of the two zero runs are the multiples of `p` in `(k, k + rn]`
and in `(n - k, (1+r)n - k]`. -/
lemma cfun_eq_cp (m p k : ℕ) (hp : 0 < p) :
    cfun ((nOf m : ℚ) / p) ((k : ℚ) / p) = cp m p k := by
  have hpq : (p : ℚ) ≠ 0 := by
    have : (0 : ℚ) < p := by exact_mod_cast hp
    exact this.ne'
  -- the counts
  have h1 : (#{l ∈ Icc (1 : ℤ) (220 * ((m : ℤ) + 1)) | (p : ℤ) ∣ (k : ℤ) + l} : ℤ) =
      flp p ((k : ℤ) + 220 * ((m : ℤ) + 1)) - flp p (k : ℤ) := by
    have := card_Icc_dvd hp 1 (220 * ((m : ℤ) + 1)) (-(k : ℤ)) (by omega)
    have hf : (Icc (1 : ℤ) (220 * ((m : ℤ) + 1))).filter (fun l => (p : ℤ) ∣ (k : ℤ) + l) =
        (Icc (1 : ℤ) (220 * ((m : ℤ) + 1))).filter (fun l => (p : ℤ) ∣ l - -(k : ℤ)) := by
      apply Finset.filter_congr; intro l _; rw [show l - -(k : ℤ) = (k : ℤ) + l by ring]
    rw [hf, this, show 220 * ((m : ℤ) + 1) - -(k : ℤ) = (k : ℤ) + 220 * ((m : ℤ) + 1) by ring,
      show (1 : ℤ) - 1 - -(k : ℤ) = k by ring]
  have h2 : (#{l ∈ Icc ((nOf m : ℤ) + 1) (460 * ((m : ℤ) + 1)) | (p : ℤ) ∣ l - k} : ℤ) =
      flp p (460 * ((m : ℤ) + 1) - k) - flp p ((nOf m : ℤ) - k) := by
    rw [card_Icc_dvd hp _ _ _ (by unfold nOf; push_cast; omega),
      show (nOf m : ℤ) + 1 - 1 - (k : ℤ) = (nOf m : ℤ) - k by ring]
  unfold cp
  push_cast
  rw [h1, h2]
  unfold cfun flp rr nOf
  have e1 : (k : ℚ) / p + 11 / 12 * ((((240 * (m + 1) : ℕ) : ℚ)) / p) =
      (((k : ℤ) + 220 * ((m : ℤ) + 1) : ℤ) : ℚ) / ((p : ℤ) : ℚ) := by
    push_cast; field_simp; ring
  have e2 : (k : ℚ) / p = ((k : ℤ) : ℚ) / ((p : ℤ) : ℚ) := by simp
  have e3 : (k : ℚ) / p - (((240 * (m + 1) : ℕ) : ℚ)) / p =
      -((((240 * (m + 1) : ℕ) : ℤ) - k : ℤ) : ℚ) / ((p : ℤ) : ℚ) := by
    push_cast; field_simp; ring
  have e4 : (k : ℚ) / p - (1 + 11 / 12) * ((((240 * (m + 1) : ℕ) : ℚ)) / p) =
      -((460 * ((m : ℤ) + 1) - k : ℤ) : ℚ) / ((p : ℤ) : ℚ) := by
    push_cast; field_simp; ring
  rw [e1, e3, e4, ← e2, neg_div, neg_div, Int.ceil_neg, Int.ceil_neg]
  ring

/-- `B_k ≥ 1` forces `k ≤ n`. -/
lemma le_nOf_of_Bk (m k : ℕ) (hk : 1 ≤ Bk m k) : k ≤ nOf m := by
  by_contra h
  push_neg at h
  have : Bk m k = 0 := by
    unfold Bk
    apply List.sum_eq_zero
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    rw [if_neg]
    omega
  omega

/-! ## Lemma 5, pointwise part -/

/-- `e_p(k)` is the Lemma 5 bracket at `x = n/p`, `y = k/p`. -/
lemma epk_eq_bracket (m p k : ℕ) (hp : 0 < p) :
    epk m p k = bracket ((nOf m : ℚ) / p) ((k : ℚ) / p) := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hy : (1 ≤ (k : ℚ) / p) ↔ p ≤ k := by
    rw [le_div_iff₀ hp', one_mul]; exact Nat.cast_le
  unfold epk bracket
  rw [Sfun_eq_Bk m p k hp, Ptot_eq_Pp m p k hp, cfun_eq_cp m p k hp]
  simp only [hy]

/-- **Lemma 5, pointwise part, for Z7.** For `n = 240(m+1)`, `0 < p ≤ n` and `k` with
`B_k ≥ 1`: `e_p(k) - G ⌊n/p⌋ ≤ e*(n/p)`. -/
theorem pointwise_le_eStar (m p k : ℕ) (hp : 0 < p) (hpn : p ≤ nOf m) (hk : 1 ≤ Bk m k) :
    (epk m p k : ℚ) - G * ⌊(nOf m : ℚ) / p⌋ ≤ eStar ((nOf m : ℚ) / p) := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hkn : k ≤ nOf m := le_nOf_of_Bk m k hk
  have hx1 : 1 ≤ (nOf m : ℚ) / p := by
    rw [le_div_iff₀ hp', one_mul]; exact_mod_cast hpn
  have hy0 : 0 ≤ (k : ℚ) / p := by positivity
  have hyx : (k : ℚ) / p ≤ (nOf m : ℚ) / p :=
    div_le_div_of_nonneg_right (by exact_mod_cast hkn) hp'.le
  have hS : 1 ≤ Sfun ((nOf m : ℚ) / p) ((k : ℚ) / p) := by rw [Sfun_eq_Bk m p k hp]; exact hk
  have h := bracket_le_eStarInt _ _ hy0 hyx hS
  rw [← epk_eq_bracket m p k hp] at h
  rw [eStar, if_pos hx1]
  have : (epk m p k : ℚ) ≤ eStarInt ((nOf m : ℚ) / p) := by exact_mod_cast h
  linarith

/-- The same for primes. -/
theorem pointwise_le_eStar_prime (m p k : ℕ) (hp : p.Prime) (hpn : p ≤ nOf m)
    (hk : 1 ≤ Bk m k) :
    (epk m p k : ℚ) - G * ⌊(nOf m : ℚ) / p⌋ ≤ eStar ((nOf m : ℚ) / p) :=
  pointwise_le_eStar m p k hp.pos hpn hk

end ZetaIrr.Z7.CertA
