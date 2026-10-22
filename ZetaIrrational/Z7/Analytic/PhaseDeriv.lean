/-
# Derivatives of the phase `f = Ψ - 3πix` and holomorphy of the amplitude `A` (Z7)

In the upper half plane every `α_i(x) = s_i x + u_i` lies in the slit plane, and

    Ψ' = Σ c_i s_i log α_i,   Ψ'' = Σ c_i s_i²/α_i,   Ψ''' = -Σ c_i s_i³/α_i²

(`hasDerivAt_PsiZ`, `hasDerivAt_Psi1Z`, `hasDerivAt_Psi2Z`; the first uses `Σ c_i s_i = 0`).
`Alim` (the limiting amplitude) is holomorphic there (`differentiableAt_Alim`).
-/
import ZetaIrrational.Z7.Analytic.Path

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Real Finset Filter Topology
open ZetaIrr.Analytic ZetaIrr.Fam.Analytic

lemma sZ_ne_zero (i : Fin 40) : sZ i ≠ 0 := by
  intro h; have := sZ_sq i; rw [h] at this; norm_num at this

lemma alphaZ_im (i : Fin 40) (x : ℂ) : (alphaZ i x).im = sZ i * x.im := by
  simp [alphaZ]

lemma alphaZ_slit (i : Fin 40) {x : ℂ} (hx : x.im ≠ 0) : alphaZ i x ∈ slitPlane :=
  Or.inr (by rw [alphaZ_im]; exact mul_ne_zero (sZ_ne_zero i) hx)

lemma alphaZ_ne_zero (i : Fin 40) {x : ℂ} (hx : x.im ≠ 0) : alphaZ i x ≠ 0 :=
  slitPlane_ne_zero (alphaZ_slit i hx)

lemma hasDerivAt_alphaZ (i : Fin 40) (x : ℂ) : HasDerivAt (alphaZ i) (sZ i) x := by
  have := ((hasDerivAt_id x).const_mul (sZ i : ℂ)).add_const (uZ i : ℂ)
  have hf : alphaZ i = fun y => (sZ i : ℂ) * id y + (uZ i : ℂ) := by funext y; simp [alphaZ]
  rw [hf]
  exact this.congr_deriv (by simp)

lemma hasDerivAt_PsiZ {x : ℂ} (hx : x.im ≠ 0) : HasDerivAt PsiZ (Psi1Z x) x := by
  have h : ∀ i ∈ (univ : Finset (Fin 40)), HasDerivAt
      (fun y => (cZ i : ℂ) * (alphaZ i y * Complex.log (alphaZ i y)))
      ((cZ i : ℂ) * (sZ i * Complex.log (alphaZ i x) + sZ i)) x := by
    intro i _
    have hα := hasDerivAt_alphaZ i x
    have hl := hα.clog (alphaZ_slit i hx)
    have := (hα.mul hl).const_mul (cZ i : ℂ)
    refine this.congr_deriv ?_
    have hne := alphaZ_ne_zero i hx
    field_simp
  have hs := HasDerivAt.fun_sum h
  unfold PsiZ
  refine hs.congr_deriv ?_
  unfold Psi1Z
  rw [← sub_eq_zero, ← sum_sub_distrib]
  have : ∑ i, ((cZ i : ℂ) * (sZ i * Complex.log (alphaZ i x) + sZ i)
      - (cZ i : ℂ) * sZ i * Complex.log (alphaZ i x)) = ∑ i, (cZ i : ℂ) * sZ i :=
    sum_congr rfl (fun i _ => by ring)
  rw [this, sum_cs_C]

lemma hasDerivAt_Psi1Z {x : ℂ} (hx : x.im ≠ 0) : HasDerivAt Psi1Z (Psi2Z x) x := by
  have h : ∀ i ∈ (univ : Finset (Fin 40)), HasDerivAt
      (fun y => (cZ i : ℂ) * sZ i * Complex.log (alphaZ i y))
      ((cZ i : ℂ) * sZ i ^ 2 / alphaZ i x) x := by
    intro i _
    have hl := (hasDerivAt_alphaZ i x).clog (alphaZ_slit i hx)
    have := hl.const_mul ((cZ i : ℂ) * sZ i)
    refine this.congr_deriv ?_
    have hne := alphaZ_ne_zero i hx
    field_simp
  exact HasDerivAt.fun_sum h

lemma hasDerivAt_Psi2Z {x : ℂ} (hx : x.im ≠ 0) : HasDerivAt Psi2Z (Psi3Z x) x := by
  have h : ∀ i ∈ (univ : Finset (Fin 40)), HasDerivAt
      (fun y => (cZ i : ℂ) * sZ i ^ 2 / alphaZ i y)
      (-((cZ i : ℂ) * sZ i ^ 3 / alphaZ i x ^ 2)) x := by
    intro i _
    have hne := alphaZ_ne_zero i hx
    have := ((hasDerivAt_alphaZ i x).inv hne).const_mul ((cZ i : ℂ) * sZ i ^ 2)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
    · field_simp
    · exact Eventually.of_forall (fun y => by simp [div_eq_mul_inv])
  have hs := HasDerivAt.fun_sum h
  unfold Psi2Z
  refine hs.congr_deriv ?_
  unfold Psi3Z
  rw [sum_neg_distrib]

lemma hasDerivAt_phaseZ {x : ℂ} (hx : x.im ≠ 0) :
    HasDerivAt phaseZ (Psi1Z x - 3 * π * I) x := by
  have := (hasDerivAt_PsiZ hx).fun_sub ((hasDerivAt_id x).const_mul (3 * π * I : ℂ))
  have hf : phaseZ = fun y => PsiZ y - 3 * π * I * id y := by funext y; simp [phaseZ]
  rw [hf]
  exact this.congr_deriv (by simp)

lemma differentiableAt_psi0Z {x : ℂ} (hx : x.im ≠ 0) : DifferentiableAt ℂ psi0Z x := by
  unfold psi0Z
  refine DifferentiableAt.fun_sum (fun i _ => ?_)
  exact ((hasDerivAt_alphaZ i x).clog (alphaZ_slit i hx)).differentiableAt.const_mul _

lemma differentiableAt_Alim {x : ℂ} (hx : x.im ≠ 0) : DifferentiableAt ℂ Alim x := by
  have h1 := differentiableAt_psi0Z hx
  have h3 : DifferentiableAt ℂ (fun y : ℂ => 2 * y + 1) x := by fun_prop
  unfold Alim
  exact h3.mul h1.cexp

lemma differentiableOn_Alim : DifferentiableOn ℂ Alim {x : ℂ | 0 < x.im} :=
  fun x hx => (differentiableAt_Alim (ne_of_gt hx)).differentiableWithinAt

end ZetaIrr.Z7.Analytic
