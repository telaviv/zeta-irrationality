/-
# Glue (Z7): Lemmas 3, 4, 5 discharged — `oneOfZeta7To21_of_parts`

`Z7.Hyp` (`FamilyZ7.lean`) is built from:
* Lemma 3 (`expansion`): `expansion_Z7` (`Z7/Concrete/Expansion.lean`), with `ρ = (pf m).rho`,
  `τ m j = (pf m).tau (2j-3)`;
* Lemma 4 (`D`, `D_pos`, `int_ρ`, `int_τ`): `Arith.D`, `D_pos_Z7`, `int_rho_Z7`, `int_tau_Z7`
  (`Z7/Arith/Lemma4.lean`);
* Lemmas 4–5 (`arith`, with `A = Acert`): `arith_Z7`, from the split `Arith.log_D_sub_le`
  (`O(√n log n)` + the sharp sum) and `sharp_Z7` (PNT step `sharp_of_pointwise` with the CertA
  data: pointwise bound, step function on the events of `[1, 400]`, tail `33 + G{y}`);
* the A-certificate: the single computational fact `hcert : CertA.CertFact`
  (`ABody 400 + tail 400 ≤ Acert`, `Z7/CertA/Cert.lean`), taken as a hypothesis (proved by the
  kernel in `Z7/CertAK/CertCompute.lean`);
* Lemma 6(i) (`size`) and 6(ii) (`nonvan`): hypotheses (discharged by `Z7/Lemma6.lean`).

Main result: `oneOfZeta7To21_of_parts (hcert) (εL) (hεL) (hsize) (hnon) : OneOfZeta7To21`.
-/
import ZetaIrrational.Z7.Glue.CertInst
import ZetaIrrational.Z7.CertA.Cert
import ZetaIrrational.Z7.Arith.Lemma4
import ZetaIrrational.Z7.Concrete.Expansion
import ZetaIrrational.FamilyZ7

namespace ZetaIrr.Z7

open Filter Topology Finset

/-- (c) of `sharp_of_pointwise` for the CertA data: `A_body + 33/400 + G/(2·399) ≤ Acert`. -/
lemma cert_Z7 (hcert : CertA.CertFact) :
    ∑ i ∈ range (LL (CertA.events 400)),
      uL (CertA.events 400) i * (1 / xL (CertA.events 400) i - 1 / xL (CertA.events 400) (i + 1))
      + 33 / ((400 : ℕ) : ℝ) + (G : ℝ) / (2 * (((400 : ℕ) : ℝ) - 1)) ≤ (Acert : ℝ) := by
  rw [← pairSum_cast_eq]
  have h : CertA.ABody 400 + CertA.tail 400 ≤ Acert := hcert
  unfold CertA.tail CertA.ABody at h
  generalize CertA.pairSum (fun a b => CertA.eStar ((a + b) / 2) * (1 / a - 1 / b))
    (CertA.events 400) = P at h ⊢
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h' ⊢
  linarith

/-- **Lemma 5 for Z7** (given the A-certificate `hcert`). `Σ_{√𝒩 < p ≤ n} (E_p - G⌊n/p⌋) log p ≤ n (Acert + o(1))`. -/
theorem sharp_Z7 (hcert : CertA.CertFact) :
    ∃ εS : ℕ → ℝ, Tendsto εS atTop (𝓝 0) ∧
    ∀ᶠ m in atTop,
      ∑ p ∈ Arith.sharpPrimes m,
          ((Arith.Esharp m p : ℝ) - (G : ℝ) * ((nOf m / p : ℕ) : ℝ)) * Real.log p
        ≤ (nOf m : ℝ) * ((Acert : ℝ) + εS m) :=
  sharp_of_pointwise (fun q => ((CertA.eStar q : ℚ) : ℝ))
    (Eventually.of_forall fun m p hp hpn _ => Esharp_sub_le_eStar m p hp hpn)
    (xL (CertA.events 400)) (uL (CertA.events 400)) (LL (CertA.events 400)) 400 (by norm_num)
    (xL_zero evs_pairwise evs_bounds one_mem_evs four_hundred_mem_evs) (xL_lt evs_pairwise)
    (xL_LL evs_pairwise evs_bounds one_mem_evs four_hundred_mem_evs) cell_le_evs 33 (by norm_num)
    tail_le
    (Acert : ℝ) (cert_Z7 hcert)

/-- **Lemmas 4–5 for Z7** (given the A-certificate `hcert`): `log D_n ≤ G log n! + n (Acert + εA)` with `εA → 0`. -/
theorem arith_Z7 (hcert : CertA.CertFact) :
    ∃ εA : ℕ → ℝ, Tendsto εA atTop (𝓝 0) ∧
    ∀ᶠ m in atTop, Real.log ((Arith.D m : ℚ) : ℝ)
      ≤ (G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * ((Acert : ℝ) + εA m) := by
  obtain ⟨εS, hεS, hsharp⟩ := sharp_Z7 hcert
  refine ⟨fun m => εS m
      + 182 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) / nOf m, ?_, ?_⟩
  · have := hεS.add tendsto_err2
    rw [add_zero] at this
    exact this
  · filter_upwards [hsharp] with m hm
    have hsplit := Arith.log_D_sub_le m
    have hn := nOf_pos m
    have e2 : (nOf m : ℝ) * (182 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) / nOf m)
        = 182 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) := by
      field_simp
    have e3 : (nOf m : ℝ) * ((Acert : ℝ) + (εS m
        + 182 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) / nOf m))
        = (nOf m : ℝ) * ((Acert : ℝ) + εS m)
          + (nOf m : ℝ) * (182 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) / nOf m) := by
      ring
    rw [e3, e2]
    linarith

/-- `Z7.Hyp` from the parts: the A-certificate `hcert`, Lemma 6(i) `hsize`, Lemma 6(ii)
`hnon`. -/
noncomputable def hypOfParts (hcert : CertA.CertFact)
    (εL : ℕ → ℝ) (hεL : Tendsto εL atTop (𝓝 0))
    (hsize : ∀ᶠ m in atTop, L m ≠ 0 → Real.log |L m| ≤
      -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * ((Vcert : ℝ) + εL m))
    (hnon : ∃ᶠ m in atTop, L m ≠ 0) : Hyp where
  ρ := fun m => (pf m).rho
  τ := fun m j => (pf m).tau (2 * j - 3)
  expansion := expansion_Z7
  D := Arith.D
  D_pos := Arith.D_pos_Z7
  int_ρ := Arith.int_rho_Z7
  int_τ := Arith.int_tau_Z7
  A := Acert
  hA := le_rfl
  εA := (arith_Z7 hcert).choose
  εA_lim := (arith_Z7 hcert).choose_spec.1
  arith := (arith_Z7 hcert).choose_spec.2
  εL := εL
  εL_lim := hεL
  size := hsize
  nonvan := hnon

/-- **Main theorem for Z7 from the parts.** Given the single computational fact `hcert`
(the A-certificate), Lemma 6(i) (`hsize`, with `V_cert = -10.1167`) and Lemma 6(ii) (`hnon`), one of
`ζ(7), ζ(9), …, ζ(21)` is irrational. -/
theorem oneOfZeta7To21_of_parts (hcert : CertA.CertFact)
    (εL : ℕ → ℝ) (hεL : Tendsto εL atTop (𝓝 0))
    (hsize : ∀ᶠ m in atTop, L m ≠ 0 → Real.log |L m| ≤
      -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * ((Vcert : ℝ) + εL m))
    (hnon : ∃ᶠ m in atTop, L m ≠ 0) : OneOfZeta7To21 :=
  oneOfZeta7To21_of_hyp (hypOfParts hcert εL hεL hsize hnon)

end ZetaIrr.Z7
