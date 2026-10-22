/-
# Lemma 4 for instance Z7: `D_n ρ_n, D_n τ_i ∈ ℤ`

For each prime `p` we show `v_p(τ_i) ≥ -E_p` and `v_p(ρ) ≥ -E_p`, in three regimes:
* `p > n`: `a_int` (Lemma A(a)) and Lemma B (`H_k^{(j)}` is `p`-integral, `k ≤ n < p`);
* `√𝒩 < p ≤ n` (`𝒩 < p²`): `bounds_sharp`, from `a_bound_sharp` (Lemma A(b), slope 1), Lemma A(b′)
  (`a_int_of_nodvd`: no pole of a block at a distance `≡ 0 (mod p)` gives `a_{i,k} ∈ ℤ_p`), and
  Lemma B (`v_p(H_k^{(j)}) ≥ -j` for `k < p²`; `H_k^{(j)} ∈ ℤ_p` for `k < p`);
* `p ≤ √𝒩`: `bounds_small` (Lemma A(c), slope `λ = ⌊log_p 𝒩⌋`).

Main theorems:
* `int_tau (m i) : ∃ z : ℤ, (z : ℚ) = D m * (pf m).tau i`;
* `int_rho (m) : ∃ z : ℤ, (z : ℚ) = D m * (pf m).rho`.
-/
import ZetaIrrational.Z7.Arith.Ep

set_option linter.unusedSectionVars false

namespace ZetaIrr.Z7.Arith

open Finset ZetaIrr.Arith
open ZetaIrr.PFData (Hq)

variable {p : ℕ} [hp : Fact p.Prime]

lemma pf_K (m : ℕ) : (pf m).K = nOf m := rfl
lemma pf_a (m : ℕ) : (pf m).a = a m := rfl

lemma a_eq_zero_of_not {m i k : ℕ} (h : ¬ (1 ≤ i ∧ i ≤ Bk m k)) : a m i k = 0 := by
  rw [a, if_neg h]

/-! ### Lemma A(a), (b′): integrality -/

/-- **Lemma A(b′)** (and A(a)): if no pole of a block lies at a distance `≡ 0 (mod p)` from
`-k`, then `a_{i,k}` is `p`-integral. -/
theorem a_int_of_nodvd (m i k : ℕ) (hk : k ≤ nOf m)
    (hnd : ∀ b ∈ blocks, ∀ k' ∈ (blk m b).erase k, ¬ (p : ℤ) ∣ (k' : ℤ) - k) :
    vge p 0 (a m i k) := by
  have h := vge_a (p := p) m i k 0 0 (fun _ => 0) (fun _ => 0)
    (by rw [e_cast]; exact vge_int _)
    (by simpa using vge_nat (p := p) 2)
    (fun z hz => ⟨by rw [zv_cast]; exact vge_int _, le_rfl⟩)
    (fun b hb k' hk' => by
      rw [d_cast, padicValRat_int_eq_zero (hnd b hb k' hk')]
      simp)
  have he : etot m k 0 (fun _ => 0) (fun _ => 0) = 0 := by simp [etot]
  rw [he, zero_mul, sub_zero] at h
  exact h

/-- **Lemma A(a).** For `p > n`, `a_{i,k}` is `p`-integral. -/
theorem a_int (m : ℕ) (hpn : nOf m < p) (i k : ℕ) (hk : k ≤ nOf m) : vge p 0 (a m i k) := by
  refine a_int_of_nodvd m i k hk (fun b _ k' hk' hd => ?_)
  have hne : k' ≠ k := ne_of_mem_erase hk'
  have hk'n : k' ≤ nOf m := mem_blk_le (mem_of_mem_erase hk')
  have hd0 : ((k' : ℤ) - k) ≠ 0 := by omega
  have h1 : p ∣ ((k' : ℤ) - k).natAbs := Int.natCast_dvd.mp hd
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hd0) h1
  have := d_natAbs_le m k k' hk hk'n
  omega

/-! ### Lemma A(b): the sharp range -/

theorem a_bound_sharp (m : ℕ) (hN : NN m < p ^ 2) (i k : ℕ) (hk : k ≤ nOf m) :
    vge p (eSharp m p k - ((Bk m k : ℤ) - i)) (a m i k) := by
  have h := vge_a (p := p) m i k 1 (if (p : ℤ) ∣ (nOf m : ℤ) - 2 * k then 1 else 0)
    (fun z => if (p : ℤ) ∣ zv k z then 1 else 0)
    (fun k' => -(if (p : ℤ) ∣ (k' : ℤ) - k then 1 else 0))
    (by rw [e_cast]; exact vge_ind_int _)
    (vge_mono (by simpa using vge_nat (p := p) 2) (by split_ifs <;> norm_num))
    (fun z _ => ⟨by rw [zv_cast]; exact vge_ind_int _, by split_ifs <;> norm_num⟩)
    (fun b _ k' hk' => by
      have hne : k' ≠ k := ne_of_mem_erase hk'
      have hk'n : k' ≤ nOf m := mem_blk_le (mem_of_mem_erase hk')
      have hd0 : ((k' : ℤ) - k) ≠ 0 := by omega
      have hlt : ((k' : ℤ) - k).natAbs < p ^ 2 := by
        have := d_natAbs_le m k k' hk hk'n; have := nOf_lt_NN m; omega
      have h1 := padicValRat_int_le_ind (p := p) hd0 hlt
      rw [d_cast]
      refine ⟨by linarith, h1.trans (by split_ifs <;> norm_num)⟩)
  rw [one_mul] at h
  exact h

lemma Hq_sharp (m : ℕ) (hN : NN m < p ^ 2) (j k : ℕ) (hk : k ≤ nOf m) :
    vge p (-(j : ℤ)) (Hq j k) := by
  have h := vge_Hq (p := p) j k 1 (fun m' hm' => by
    have := padicValRat_succ_le (p := p) (m' := m') (e := 1)
      (by have := nOf_lt_NN m; rw [show 1 + 1 = 2 from rfl]; omega)
    exact_mod_cast this)
  simpa using h

/-- **Sharp range** `√𝒩 < p ≤ n`: the bounds for the `τ`- and `ρ`-terms. -/
theorem bounds_sharp (m : ℕ) (hN : NN m < p ^ 2) (i k : ℕ) (hk : k ≤ nOf m) :
    vge p (-Esharp m p) (a m i k) ∧ vge p (-Esharp m p) (a m i k * Hq (i + 4) k) := by
  by_cases hik : 1 ≤ i ∧ i ≤ Bk m k
  swap
  · rw [a_eq_zero_of_not hik, zero_mul]; exact ⟨vge_zero _, vge_zero _⟩
  have hB0 : Bk m k ≠ 0 := by omega
  have hE := eK_le_Esharp m p k hk
  have hEn := Esharp_nonneg m p
  have hA := a_bound_sharp (p := p) m hN i k hk
  rw [eSharp_eq] at hA
  have hi1 : (1 : ℤ) ≤ i := by exact_mod_cast hik.1
  by_cases hpk : p ≤ k
  · have heK : eK m p k = (Bk m k : ℤ) + 4 - cp m p k + Ptot m p k := by
      rw [eK, if_neg hB0, if_pos hpk]
    have hH := Hq_sharp m hN (i + 4) k hk
    refine ⟨vge_mono hA (by push_cast at heK ⊢; linarith),
      vge_mono (vge_mul hA hH) (by push_cast at heK ⊢; linarith)⟩
  · have hH := vge_Hq_of_lt (p := p) (i + 4) k (by omega)
    by_cases hP : Ptot m p k = 0
    · have hint := a_int_of_nodvd (p := p) m i k hk (not_dvd_of_Ptot_eq_zero hP)
      exact ⟨vge_mono hint (by linarith), vge_mono (vge_mul hint hH) (by linarith)⟩
    · have heK : eK m p k = (Bk m k : ℤ) - 1 - cp m p k + Ptot m p k := by
        rw [eK, if_neg hB0, if_neg hpk, if_neg hP]
      refine ⟨vge_mono hA (by push_cast at heK ⊢; linarith),
        vge_mono (vge_mul hA hH) (by push_cast at heK ⊢; linarith)⟩

/-! ### Lemma A(c): the small primes -/

lemma NN_lt_pow_log (m : ℕ) : NN m < p ^ (Nat.log p (NN m) + 1) :=
  Nat.lt_pow_succ_log_self hp.out.one_lt _

theorem a_bound_small (m i k : ℕ) (hk : k ≤ nOf m) :
    vge p (nuSmall m p k - (Nat.log p (NN m) : ℤ) * ((Bk m k : ℤ) - i)) (a m i k) := by
  have hlog := NN_lt_pow_log (p := p) m
  have h := vge_a (p := p) m i k (Nat.log p (NN m) : ℤ) 0
    (fun z => (padicValInt p (zv k z) : ℤ))
    (fun k' => -(padicValInt p ((k' : ℤ) - k) : ℤ))
    (by rw [e_cast]; exact vge_int _)
    (vge_mono (by simpa using vge_nat (p := p) 2) (by omega))
    (fun z hz => by
      refine ⟨?_, ?_⟩
      · rw [zv_cast]
        intro _; rw [padicValRat.of_int]
      · have := padicValRat_int_le (p := p) (zv_ne_zero m k hk z hz)
          (e := Nat.log p (NN m)) ((zv_natAbs_lt m k hk z hz).trans hlog)
        rw [padicValRat.of_int] at this
        exact this)
    (fun b _ k' hk' => by
      have hne : k' ≠ k := ne_of_mem_erase hk'
      have hk'n : k' ≤ nOf m := mem_blk_le (mem_of_mem_erase hk')
      have hd0 : ((k' : ℤ) - k) ≠ 0 := by omega
      have hlt : ((k' : ℤ) - k).natAbs < p ^ (Nat.log p (NN m) + 1) := by
        have := d_natAbs_le m k k' hk hk'n; have := nOf_lt_NN m; omega
      have h1 := padicValRat_int_le (p := p) hd0 hlt
      rw [d_cast]
      refine ⟨?_, h1⟩
      rw [padicValRat.of_int])
  exact h

/-- **Small primes** `p ≤ √𝒩`: the bounds for the `τ`- and `ρ`-terms. -/
theorem bounds_small (m i k : ℕ) (hk : k ≤ nOf m) :
    vge p (-Esmall m p) (a m i k) ∧ vge p (-Esmall m p) (a m i k * Hq (i + 4) k) := by
  by_cases hik : 1 ≤ i ∧ i ≤ Bk m k
  swap
  · rw [a_eq_zero_of_not hik, zero_mul]; exact ⟨vge_zero _, vge_zero _⟩
  have hlog := NN_lt_pow_log (p := p) m
  set lam : ℤ := (Nat.log p (NN m) : ℤ) with hlam
  have hA := a_bound_small (p := p) m i k hk
  have hE : -nuSmall m p k ≤ (range (nOf m + 1)).sup' nonempty_range_add_one
      (fun k => -nuSmall m p k) :=
    le_sup' (fun k => -nuSmall m p k) (mem_range.mpr (by omega))
  have hH := vge_Hq (p := p) (i + 4) k lam (fun m' hm' => by
    have := padicValRat_succ_le (p := p) (m' := m') (e := Nat.log p (NN m))
      (by have := nOf_lt_NN m; omega)
    rw [hlam]; exact this)
  have hl0 : 0 ≤ lam := by positivity
  have hBk : (Bk m k : ℤ) ≤ 18 := by exact_mod_cast Bk_le m k
  have hi1 : (1 : ℤ) ≤ i := by exact_mod_cast hik.1
  have hiB : (i : ℤ) ≤ Bk m k := by exact_mod_cast hik.2
  unfold Esmall
  refine ⟨vge_mono hA ?_, vge_mono (vge_mul hA hH) ?_⟩
  · push_cast; nlinarith
  · push_cast; nlinarith

/-! ### Assembly -/

theorem bounds_all (m : ℕ) (hpn : p ≤ nOf m) (i k : ℕ) (hk : k ≤ nOf m) :
    vge p (-Ep m p) (a m i k) ∧ vge p (-Ep m p) (a m i k * Hq (i + 4) k) := by
  have hpn' : ¬ nOf m < p := by omega
  unfold Ep
  simp only [hpn', ite_false]
  split_ifs with hN
  · exact bounds_sharp m hN i k hk
  · exact bounds_small m i k hk

theorem vge_tau_Ep (m i : ℕ) : vge p (-Ep m p) ((pf m).tau i) := by
  refine vge_tau (pf m) i _ (fun k hk => ?_)
  rw [pf_a]
  rw [pf_K] at hk
  by_cases hq : nOf m < p
  · rw [Ep_eq_zero_of_lt hq, neg_zero]
    exact a_int m hq i k hk
  · exact (bounds_all m (by omega) i k hk).1

theorem vge_rho_Ep (m : ℕ) : vge p (-Ep m p) (pf m).rho := by
  refine vge_rho (pf m) _ (fun k hk i _ => ?_)
  rw [pf_a]
  rw [pf_K] at hk
  by_cases hq : nOf m < p
  · rw [Ep_eq_zero_of_lt hq, neg_zero]
    simpa using vge_mul (a_int m hq i k hk) (vge_Hq_of_lt (p := p) (i + 4) k (by omega))
  · exact (bounds_all m (by omega) i k hk).2

/-- **Lemma 4 (τ part).** `D_n τ_i ∈ ℤ` for every `i`. -/
theorem int_tau (m i : ℕ) : ∃ z : ℤ, (z : ℚ) = D m * (pf m).tau i :=
  int_of_vge_Ep m (fun q hq => by have : Fact q.Prime := ⟨hq⟩; exact vge_tau_Ep m i)

/-- **Lemma 4 (ρ part).** `D_n ρ_n ∈ ℤ`. -/
theorem int_rho (m : ℕ) : ∃ z : ℤ, (z : ℚ) = D m * (pf m).rho :=
  int_of_vge_Ep m (fun q hq => by have : Fact q.Prime := ⟨hq⟩; exact vge_rho_Ep m)

end ZetaIrr.Z7.Arith
