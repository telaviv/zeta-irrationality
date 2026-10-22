/-
# Lemma A for instance Z7: valuations of the Taylor coefficients `a_{i,k}`

For the data of `Z7/Concrete/Data.lean`:

`fSeries m k = (C(n-2k) + 2X) · Π_{z ∈ Zs} (C(-k-z) + X)^5 · Π_j (Π_{k' ∈ block j, k'≠k} (C(k'-k) + X)⁻¹)^{m_j}`.

`psge_fSeries` is the binomial argument with free per-factor exponents: if each zero factor gets
an exponent `eZ z ≤ λ` with `v_p(-k-z) ≥ eZ z`, each pole factor (only those in a block) an exponent
`eP k' ≤ -v_p(k'-k)` with `v_p(k'-k) ≤ λ`, and the e-factor an exponent `eE` with
`v_p(n-2k) ≥ eE` (or `n = 2k`) and `v_p(2) ≥ eE - λ`, then
`v_p([X^M] f_k) ≥ eE + 5 Σ_z eZ z + Σ_j m_j Σ_{k'} eP k' - λ M`.

`vge_a` turns this into the bound on `a_{i,k} = [X^{B_k - i}] f_k`. The regimes of Lemma A(a),
(b), (b′), (c) are instances (file `Ep.lean`). Because the pole hypothesis only concerns the
poles *in a block* (the factors actually present), (b′) — "no pole at a distance `≡ 0 (mod p)`
gives `a_{i,k} ∈ ℤ_p`" — is the instance `λ = 0`.
-/
import ZetaIrrational.Arith.PSVal
import ZetaIrrational.Z7.Concrete.Expansion

set_option linter.unusedSectionVars false

namespace ZetaIrr.Z7.Arith

open Finset PowerSeries ZetaIrr.Arith

variable {p : ℕ} [hp : Fact p.Prime]

lemma mem_blk_le {m k' : ℕ} {b : ℕ × ℕ} (h : k' ∈ blk m b) : k' ≤ nOf m := by
  simp only [blk, mem_Icc] at h; omega

/-- `numSeries` written over the zero set `Zs`. -/
lemma numSeries_eq_Zs (m k : ℕ) : numSeries m k =
    (C ((nOf m : ℚ) - 2 * k) + 2 * X) * ∏ z ∈ Zs m, (C (-(k : ℚ) - z) + X) ^ 5 := by
  rw [prod_Zs, numSeries, mul_assoc]
  have h1 : ∏ l ∈ Icc 1 (220 * (m + 1)), (C (-(k : ℚ) - l) + X) ^ 5
      = ∏ l ∈ Icc 1 (220 * (m + 1)), (C (-(k : ℚ) - (((l : ℤ) : ℤ) : ℚ)) + X) ^ 5 := by
    refine prod_congr rfl (fun l _ => ?_)
    simp only [Int.cast_natCast]
  have h2 : ∏ l ∈ Icc (nOf m + 1) (460 * (m + 1)), (C ((l : ℚ) - k) + X) ^ 5
      = ∏ l ∈ Icc (nOf m + 1) (460 * (m + 1)), (C (-(k : ℚ) - ((-(l : ℤ) : ℤ) : ℚ)) + X) ^ 5 := by
    refine prod_congr rfl (fun l _ => ?_)
    rw [show -(k : ℚ) - ((-(l : ℤ) : ℤ) : ℚ) = (l : ℚ) - k by push_cast; ring]
  rw [h1, h2]

/-- The total exponent of the binomial argument. -/
def etot (m k : ℕ) (eE : ℤ) (eZ : ℤ → ℤ) (eP : ℕ → ℤ) : ℤ :=
  eE + ∑ z ∈ Zs m, 5 * eZ z +
    (blocks.map (fun b => (b.2 : ℤ) * ∑ k' ∈ (blk m b).erase k, eP k')).sum

/-- **Lemma A (binomial argument), general form.** -/
theorem psge_fSeries (m k : ℕ) (lam eE : ℤ) (eZ : ℤ → ℤ) (eP : ℕ → ℤ)
    (hE1 : vge p eE ((nOf m : ℚ) - 2 * k)) (hE2 : vge p (eE - lam) 2)
    (hZ : ∀ z ∈ Zs m, vge p (eZ z) (-(k : ℚ) - z) ∧ eZ z ≤ lam)
    (hP : ∀ b ∈ blocks, ∀ k' ∈ (blk m b).erase k,
      eP k' ≤ -padicValRat p ((k' : ℚ) - k) ∧ padicValRat p ((k' : ℚ) - k) ≤ lam) :
    psge p (etot m k eE eZ eP) lam (fSeries m k) := by
  unfold fSeries etot
  rw [numSeries_eq_Zs]
  unfold denSeries
  refine psge_mul (psge_mul ?_ ?_) ?_
  · have h2 : (2 : PowerSeries ℚ) = C 2 := (map_ofNat C 2).symm
    rw [h2]
    exact psge_lin hE1 hE2
  · refine psge_prod _ _ _ lam (fun z hz => ?_)
    have h := psge_pow (psge_lin (p := p) (lam := lam) (c := 1) (hZ z hz).1
      (by intro _; simp; linarith [(hZ z hz).2])) 5
    simp only [map_one, one_mul] at h
    simpa using h
  · refine psge_listProd blocks _ _ lam (fun b hb => ?_)
    have h := psge_pow (psge_prod (p := p) ((blk m b).erase k) _ eP lam (fun k' hk' => by
      have hk'1 : k' ≠ k := ne_of_mem_erase hk'
      have hd : ((k' : ℚ) - k) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hk'1)
      exact psge_inv hd (hP b hb k' hk').1 (hP b hb k' hk').2)) b.2
    exact h

/-- **Lemma A, coefficient form.** `v_p(a_{i,k}) ≥ etot - λ (B_k - i)`. -/
theorem vge_a (m i k : ℕ) (lam eE : ℤ) (eZ : ℤ → ℤ) (eP : ℕ → ℤ)
    (hE1 : vge p eE ((nOf m : ℚ) - 2 * k)) (hE2 : vge p (eE - lam) 2)
    (hZ : ∀ z ∈ Zs m, vge p (eZ z) (-(k : ℚ) - z) ∧ eZ z ≤ lam)
    (hP : ∀ b ∈ blocks, ∀ k' ∈ (blk m b).erase k,
      eP k' ≤ -padicValRat p ((k' : ℚ) - k) ∧ padicValRat p ((k' : ℚ) - k) ≤ lam) :
    vge p (etot m k eE eZ eP - lam * ((Bk m k : ℤ) - i)) (a m i k) := by
  unfold a
  split_ifs with hi
  · have := psge_fSeries m k lam eE eZ eP hE1 hE2 hZ hP (Bk m k - i)
    have hc : ((Bk m k - i : ℕ) : ℤ) = (Bk m k : ℤ) - i := Nat.cast_sub hi.2
    rw [hc] at this
    exact this
  · exact vge_zero _

end ZetaIrr.Z7.Arith
