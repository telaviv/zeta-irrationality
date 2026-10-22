/-
# Lemma 4 for instance Z7: the exponents `E_p` and `D_n`

With `n = nOf m = 240(m+1)` and `𝒩 = NN m = (2+r)n + 1 = 700(m+1) + 1`:

| range of `p` | `E_p` (`Ep m p`) | source |
|---|---|---|
| `p > n` | `0` | Lemma A(a) + Lemma B |
| `√𝒩 < p ≤ n` | `max(0, max_k e_p(k))` (`Esharp`) | Lemma A(b), (b′) + Lemma B |
| `p ≤ √𝒩` | `max_k (-ν_p(k)) + 22 ⌊log_p 𝒩⌋` (`Esmall`) | Lemma A(c) + Lemma B |

with the per-`k` exponent (`eK`, only for `B_k ≥ 1`)

    e_p(k) = B_k + 4 - c_p(k) + P_p(k)    if k ≥ p,
             B_k - 1 - c_p(k) + P_p(k)    if k < p and P_p(k) ≥ 1,
             0                            if k < p and P_p(k) = 0,

`c_p(k) = Σ_z 5 [p ∣ k+z] + [p ∣ n-2k]` (`cp`), `P_p(k) = Σ_j m_j P_{p,j}(k)` (`Ptot`).
`ν_p(k) = 5 Σ_z v_p(k+z) - Σ_j m_j Σ_{k' ∈ block j, k' ≠ k} v_p(k'-k)` (`nuSmall`; this omits the
nonnegative term `v_p(n-2k)` of the e-factor, which only weakens the bound).

`D m = Π_{p ≤ n} p^{E_p}` (a positive rational).
-/
import ZetaIrrational.Z7.Arith.LemmaA
import ZetaIrrational.Arith.LemmaB

set_option linter.unusedSectionVars false

namespace ZetaIrr.Z7.Arith

open Finset ZetaIrr.Arith

/-! ### Definitions -/

/-- `𝒩 = (2+r)n + 1 = 700(m+1) + 1`. -/
def NN (m : ℕ) : ℕ := 700 * (m + 1) + 1

/-- The zero-factor constant `u_z = -k - z` at the pole `-k`. -/
def zv (k : ℕ) (z : ℤ) : ℤ := -(k : ℤ) - z

lemma zv_cast (k : ℕ) (z : ℤ) : -(k : ℚ) - z = ((zv k z : ℤ) : ℚ) := by unfold zv; push_cast; ring

lemma zv_ne_zero (m k : ℕ) (hk : k ≤ nOf m) (z : ℤ) (hz : z ∈ Zs m) : zv k z ≠ 0 := by
  rw [mem_Zs] at hz; unfold zv; unfold nOf at hk; omega

lemma zv_natAbs_lt (m k : ℕ) (hk : k ≤ nOf m) (z : ℤ) (hz : z ∈ Zs m) :
    (zv k z).natAbs < NN m := by
  rw [mem_Zs] at hz; unfold zv NN; unfold nOf at hk; omega

lemma d_natAbs_le (m k k' : ℕ) (hk : k ≤ nOf m) (hk' : k' ≤ nOf m) :
    ((k' : ℤ) - k).natAbs ≤ nOf m := by omega

lemma nOf_lt_NN (m : ℕ) : nOf m < NN m := by unfold nOf NN; omega

lemma d_cast (k k' : ℕ) : ((k' : ℚ) - k) = (((k' : ℤ) - k : ℤ) : ℚ) := by push_cast; ring

lemma e_cast (m k : ℕ) : ((nOf m : ℚ) - 2 * k) = (((nOf m : ℤ) - 2 * k : ℤ) : ℚ) := by
  push_cast; ring

/-- `c_p(k) = Σ_z μ [p ∣ k + z] + e [p ∣ n - 2k]` (here `μ = 5`, `e = 1`). -/
def cp (m p k : ℕ) : ℤ :=
  ∑ z ∈ Zs m, 5 * (if (p : ℤ) ∣ zv k z then 1 else 0) +
    (if (p : ℤ) ∣ (nOf m : ℤ) - 2 * k then 1 else 0)

/-- `P_{p,j}(k) = #{k' ∈ [a_j, b_j], k' ≠ k : p ∣ k' - k}`. -/
def Ppj (m p k : ℕ) (b : ℕ × ℕ) : ℕ :=
  (((blk m b).erase k).filter (fun k' : ℕ => (p : ℤ) ∣ (k' : ℤ) - k)).card

/-- `P_p(k) = Σ_j m_j P_{p,j}(k)`. -/
def Ptot (m p k : ℕ) : ℕ := (blocks.map (fun b => b.2 * Ppj m p k b)).sum

/-- The Lemma A(b) exponent `c_p(k) - P_p(k)` in `etot` form. -/
def eSharp (m p k : ℕ) : ℤ :=
  etot m k (if (p : ℤ) ∣ (nOf m : ℤ) - 2 * k then 1 else 0)
    (fun z => if (p : ℤ) ∣ zv k z then 1 else 0)
    (fun k' => -(if (p : ℤ) ∣ (k' : ℤ) - k then 1 else 0))

lemma list_sum_map_neg {ι : Type*} (l : List ι) (f : ι → ℤ) :
    (l.map (fun b => -f b)).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma Ptot_cast (m p k : ℕ) :
    (Ptot m p k : ℤ) = (blocks.map (fun b => (b.2 : ℤ) * (Ppj m p k b : ℤ))).sum := by
  unfold Ptot
  rw [Nat.cast_list_sum, List.map_map]
  congr 1

lemma eSharp_eq (m p k : ℕ) : eSharp m p k = cp m p k - Ptot m p k := by
  unfold eSharp etot cp
  rw [Ptot_cast]
  have h : ∀ b : ℕ × ℕ, (b.2 : ℤ) * ∑ k' ∈ (blk m b).erase k,
      -(if (p : ℤ) ∣ (k' : ℤ) - k then 1 else 0)
      = -((b.2 : ℤ) * (Ppj m p k b : ℤ)) := by
    intro b
    rw [sum_neg_distrib, Finset.sum_boole]
    unfold Ppj
    ring
  simp_rw [h]
  rw [list_sum_map_neg]
  ring

/-- `P_p(k) = 0` means: no pole of a block (other than `-k`) at a distance `≡ 0 (mod p)`. -/
lemma not_dvd_of_Ptot_eq_zero {m p k : ℕ} (h : Ptot m p k = 0) :
    ∀ b ∈ blocks, ∀ k' ∈ (blk m b).erase k, ¬ (p : ℤ) ∣ (k' : ℤ) - k := by
  intro b hb k' hk' hd
  unfold Ptot at h
  have h1 : b.2 * Ppj m p k b = 0 :=
    List.sum_eq_zero_iff.mp h _ (List.mem_map.mpr ⟨b, hb, rfl⟩)
  rw [blocks_snd b hb, one_mul] at h1
  unfold Ppj at h1
  rw [card_eq_zero, filter_eq_empty_iff] at h1
  exact h1 hk' hd

/-- `ν_p(k)` (Lemma A(c) exponent). -/
def nuSmall (m p k : ℕ) : ℤ :=
  etot m k 0 (fun z => (padicValInt p (zv k z) : ℤ)) (fun k' => -(padicValInt p ((k' : ℤ) - k) : ℤ))

/-- The per-`k` sharp exponent `e_p(k)` of Lemma 4 (`0` where `B_k = 0`). -/
def eK (m p k : ℕ) : ℤ :=
  if Bk m k = 0 then 0
  else if p ≤ k then (Bk m k : ℤ) + 4 - cp m p k + Ptot m p k
  else if Ptot m p k = 0 then 0
  else (Bk m k : ℤ) - 1 - cp m p k + Ptot m p k

/-- `E_p` for `√𝒩 < p ≤ n`: `max(0, max_k e_p(k))`. -/
def Esharp (m p : ℕ) : ℤ := max 0 ((range (nOf m + 1)).sup' nonempty_range_add_one (eK m p))

/-- `E_p` for `p ≤ √𝒩`: `max_k (-ν_p(k)) + 22 ⌊log_p 𝒩⌋`. -/
def Esmall (m p : ℕ) : ℤ :=
  (range (nOf m + 1)).sup' nonempty_range_add_one (fun k => -nuSmall m p k) +
    22 * (Nat.log p (NN m) : ℤ)

/-- The exponent `E_p` of Lemma 4. -/
def Ep (m p : ℕ) : ℤ :=
  if nOf m < p then 0
  else if NN m < p ^ 2 then Esharp m p
  else Esmall m p

lemma eK_le_Esharp (m p k : ℕ) (hk : k ≤ nOf m) : eK m p k ≤ Esharp m p :=
  le_trans (le_sup' (eK m p) (mem_range.mpr (by omega))) (le_max_right _ _)

lemma Esharp_nonneg (m p : ℕ) : 0 ≤ Esharp m p := le_max_left _ _

/-- The primes `p ≤ n`. -/
def primesD (m : ℕ) : Finset ℕ := (range (nOf m + 1)).filter Nat.Prime

/-- `D_n = Π_{p ≤ n} p^{E_p}`. -/
noncomputable def D (m : ℕ) : ℚ := ∏ p ∈ primesD m, (p : ℚ) ^ (Ep m p)

/-! ### `D` -/

theorem D_pos (m : ℕ) : 0 < D m := by
  unfold D
  refine prod_pos (fun p hp => zpow_pos ?_ _)
  exact_mod_cast (mem_filter.mp hp).2.pos

theorem Ep_eq_zero_of_lt {m p : ℕ} (h : nOf m < p) : Ep m p = 0 := by
  simp [Ep, h]

theorem padicValRat_D (m q : ℕ) [hq : Fact q.Prime] : padicValRat q (D m) = Ep m q := by
  unfold D
  rw [padicValRat_prod _ _ (fun p hp =>
    zpow_ne_zero _ (by exact_mod_cast (mem_filter.mp hp).2.ne_zero))]
  have hv : ∀ p ∈ primesD m,
      padicValRat q ((p : ℚ) ^ Ep m p) = if p = q then Ep m q else 0 := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    rw [padicValRat.zpow, padicValRat.of_nat]
    split_ifs with hpq
    · subst hpq; simp [padicValNat_self]
    · have : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp').mp h).symm
      simp [padicValNat.eq_zero_of_not_dvd this]
  rw [sum_congr rfl hv, sum_ite_eq']
  split_ifs with hmem
  · rfl
  · have : nOf m < q := by
      by_contra hc
      apply hmem
      simp only [primesD, mem_filter, mem_range]
      exact ⟨by omega, hq.out⟩
    rw [Ep_eq_zero_of_lt this]

/-- Integrality from per-prime bounds. -/
theorem int_of_vge_Ep (m : ℕ) {x : ℚ} (h : ∀ q : ℕ, q.Prime → vge q (-Ep m q) x) :
    ∃ z : ℤ, (z : ℚ) = D m * x := by
  refine int_of_forall_vge (fun q hq => ?_)
  have : Fact q.Prime := ⟨hq⟩
  have hD : vge q (Ep m q) (D m) := fun _ => (padicValRat_D m q).ge
  simpa using vge_mul hD (h q hq)

end ZetaIrr.Z7.Arith
