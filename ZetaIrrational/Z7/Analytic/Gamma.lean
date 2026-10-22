/-
# Γ-factorisation of `R_n` for instance Z7 (Lemma 6)

The complex extension `RC m` of `Z7.R m` (`RC_ofReal`), the Γ-product `En m` (`E_n`,
with `q = rn = 220(m+1)`, `Q = (1+r)n = 460(m+1)`), and

    RC m z = (2z + n) · E_n(z) · sin⁵(πz) / π⁵        (`RC_eq_En`)

for `z` not an integer (`(-1)^{5q} = 1` since `q` is even). In factor-list form (`Factors.lean`):
`RC m z = P_n(z) sin⁵(πz)/π⁵` with `P_n(z) = (2z + n) Π_i Γ(s_i z + n u_i + β_i)^{c_i}`
(`RC_eq_Pfun`).
-/
import ZetaIrrational.FamilyZ7
import ZetaIrrational.Z7.Analytic.Factors
import ZetaIrrational.Fam.Analytic.ZetaHelpers

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Real Finset
open ZetaIrr.Fam.Analytic

/-- The complex extension of `Z7.R m`. -/
noncomputable def RC (m : ℕ) (z : ℂ) : ℂ :=
  (2 * z + (Z7.nOf m : ℂ)) *
    (∏ l ∈ Icc 1 (220 * (m + 1)), (z - (l : ℂ)) ^ 5) *
    (∏ l ∈ Icc (Z7.nOf m + 1) (460 * (m + 1)), (z + (l : ℂ)) ^ 5) /
    (Z7.blocks.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (Z7.nOf m - 3 * b.1 * (m + 1)), (z + (k : ℂ))) ^ b.2)).prod

/-- `RC m` extends `Z7.R m`. -/
lemma RC_ofReal (m : ℕ) (t : ℝ) : RC m t = (Z7.R m t : ℂ) := by
  unfold RC Z7.R
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul, list_prod_map_ofReal]
  push_cast
  rfl

/-- The Γ-product `E_n(z)` for Z7. -/
noncomputable def En (m : ℕ) (z : ℂ) : ℂ :=
  Complex.Gamma z ^ 5 * Complex.Gamma (((220 * (m + 1) : ℕ) : ℂ) + 1 - z) ^ 5 *
    Complex.Gamma (z + ((460 * (m + 1) : ℕ) : ℂ) + 1) ^ 5 /
    Complex.Gamma (z + (Z7.nOf m : ℂ) + 1) ^ 5 *
    (Z7.blocks.map (fun b =>
      (Complex.Gamma (z + (3 * b.1 * (m + 1) : ℕ)) /
        Complex.Gamma (z + (Z7.nOf m - 3 * b.1 * (m + 1) : ℕ) + 1)) ^ b.2)).prod

lemma add_nat_ne_neg (z : ℂ) (hz : ∀ k : ℤ, z ≠ k) (A : ℕ) : ∀ k : ℕ, z + A ≠ -k := by
  intro k h
  apply hz (-(k : ℤ) - A)
  push_cast
  linear_combination h

/-- **Γ-factorisation for Z7.** For `z` not an integer,
`RC m z = (2z + n) E_n(z) sin⁵(πz)/π⁵`. -/
theorem RC_eq_En (m : ℕ) (z : ℂ) (hz : ∀ k : ℤ, z ≠ k) :
    RC m z = (2 * z + (Z7.nOf m : ℂ)) * En m z * Complex.sin (π * z) ^ 5 / π ^ 5 := by
  have hrun := prod_Icc_one_sub_eq_Gamma z hz (220 * (m + 1))
  have hq : ((-1 : ℂ) ^ (220 * (m + 1))) = 1 := by
    rw [pow_mul]; norm_num
  rw [hq, one_mul] at hrun
  have hrun2 := prod_Icc_add_eq_Gamma z (Z7.nOf m + 1) (460 * (m + 1))
    (by unfold Z7.nOf; omega) (add_nat_ne_neg z hz _)
  rw [Nat.cast_add, Nat.cast_one] at hrun2
  have hblk : ∀ b ∈ Z7.blocks, ∏ k ∈ Icc (3 * b.1 * (m + 1)) (Z7.nOf m - 3 * b.1 * (m + 1)),
      (z + (k : ℂ)) = Complex.Gamma (z + (Z7.nOf m - 3 * b.1 * (m + 1) : ℕ) + 1)
        / Complex.Gamma (z + (3 * b.1 * (m + 1) : ℕ)) := by
    intro b hb
    have hb1 : b.1 < 40 := (Z7.blocks_bounds b hb).2
    have hb2 : 3 * b.1 * (m + 1) ≤ 117 * (m + 1) := Nat.mul_le_mul_right _ (by omega)
    exact prod_Icc_add_eq_Gamma z _ _ (by unfold Z7.nOf; omega) (add_nat_ne_neg z hz _)
  unfold RC En
  rw [prod_pow, prod_pow, hrun, hrun2, List.map_congr_left (fun b hb => by rw [hblk b hb])]
  have hinv : (Z7.blocks.map (fun b =>
      (Complex.Gamma (z + (Z7.nOf m - 3 * b.1 * (m + 1) : ℕ) + 1)
        / Complex.Gamma (z + (3 * b.1 * (m + 1) : ℕ))) ^ b.2)).prod
      = ((Z7.blocks.map (fun b =>
      (Complex.Gamma (z + (3 * b.1 * (m + 1) : ℕ))
        / Complex.Gamma (z + (Z7.nOf m - 3 * b.1 * (m + 1) : ℕ) + 1)) ^ b.2)).prod)⁻¹ := by
    rw [← list_prod_map_inv]
    exact congrArg List.prod (List.map_congr_left (fun b _ => by rw [← inv_pow, inv_div]))
  rw [hinv, div_inv_eq_mul]
  ring

/-- `P_n(z) = (2z + n) Π_i Γ(s_i z + n u_i + β_i)^{c_i}`. -/
noncomputable def Pfun (m : ℕ) (z : ℂ) : ℂ :=
  (2 * z + (Z7.nOf m : ℂ)) *
    ∏ i, Complex.Gamma (sZ i * z + (Z7.nOf m : ℂ) * uZ i + βZ i) ^ cZ i

lemma En_eq_prod (m : ℕ) (z : ℂ) :
    En m z = ∏ i, Complex.Gamma (sZ i * z + (Z7.nOf m : ℂ) * uZ i + βZ i) ^ cZ i := by
  simp only [En, Z7.blocks, Z7.nOf, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Fin.prod_univ_succ, Fin.prod_univ_zero, cZ, sZ, uZ, βZ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, zpow_neg, zpow_ofNat, div_pow,
    Fin.succ_zero_eq_one, Matrix.cons_val_one]
  simp (disch := omega) only [Nat.cast_sub]
  push_cast
  ring_nf

/-- **Γ-factorisation in factor-list form.** -/
theorem RC_eq_Pfun (m : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    RC m z = Pfun m z * Complex.sin (π * z) ^ 5 / π ^ 5 := by
  have h1 : ∀ k : ℤ, z ≠ k := fun k h => hz (by rw [h]; simp)
  rw [RC_eq_En m z h1, En_eq_prod, Pfun]

end ZetaIrr.Z7.Analytic
