/-
# Pointwise integrand bounds (U) and (M) for instance Z7 (PROOF_ZETA §6.5)

No certificate is needed:
* `norm_Gfn_le` (the bound (U)): `|G_n(nx)| ≤ e^{λ_n + n Re f(x)} n · 72 B²`;
* `Gfn_disc_approx` (the form (M)):
  `|G_n(nx) e^{-λ_n - nΩ}/n - e^{n(f(x) - Ω)} A(x)| ≤ |e^{n(f(x)-Ω)}| · 100 B² δ_n`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Analytic.PhaseDeriv
import ZetaIrrational.Z7.Analytic.SaddleData

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Real Finset Filter Topology Set
open ZetaIrr.Analytic ZetaIrr.Fam.Analytic

/-- The "large `n`" conditions used below. -/
def LargeN (a η n : ℝ) : Prop := 4 / a ≤ n ∧ 1 ≤ n ∧ cE a η ≤ n

lemma norm_exp_lam (n : ℝ) (w : ℂ) :
    ‖Complex.exp (lamN n + (n : ℂ) * w)‖ = Real.exp (lamN n + n * w.re) := by
  rw [Complex.norm_exp]; congr 1; simp

lemma norm_q_le_one (n : ℝ) (hn : 0 ≤ n) {x : ℂ} (hx : 0 ≤ x.im) :
    ‖Complex.exp (2 * π * I * ((n : ℂ) * x))‖ ≤ 1 := by
  rw [norm_exp_two_pi_I_mul]
  apply Real.exp_le_one_iff.2
  have := Real.pi_pos
  have : 0 ≤ 2 * π * n * x.im := by positivity
  linarith

/-- **(U)**: `|G_n(nx)| ≤ e^{λ_n + n Re f(x)} n · 72 B²`. -/
theorem norm_Gfn_le (m : ℕ) {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) {x : ℂ}
    (hxim : 0 < x.im) (hx : SectorAt a η x) {R : ℝ} (hR : ‖x‖ ≤ R)
    (hn : LargeN a η (Z7.nOf m : ℝ)) :
    ‖Gfn m ((Z7.nOf m : ℝ) * x)‖ ≤ Real.exp (lamN (Z7.nOf m) + (Z7.nOf m : ℝ) * (phaseZ x).re)
      * (Z7.nOf m : ℝ) * (72 * Bgrowth a R ^ 2) := by
  obtain ⟨hn1, hn2, hn3⟩ := hn
  set n : ℝ := (Z7.nOf m : ℝ) with hn_def
  have hnpos : 0 < n := by linarith
  obtain ⟨e, he, hF⟩ := Gfn_path m ha hη0 hη hxim hx hn1
  rw [← hn_def] at hF he
  rw [hF]
  have hxsec : ∀ i, a ≤ ‖alphaZ i x‖ := fun i => (hx i).1
  obtain ⟨gX, gE⟩ := growth_bounds ha hxsec hR
  have hB : 1 ≤ Bgrowth a R := one_le_Bgrowth a ((norm_nonneg x).trans hR)
  have hq := norm_q_le_one n hnpos.le hxim.le
  have he1 : ‖e‖ ≤ 1 := he.trans (by rw [div_le_one hnpos]; exact hn3)
  have hA := amp_bound (x := x) (e := e) (q := Complex.exp (2 * π * I * ((n : ℂ) * x)))
    hB gX gE hq he1
  rw [norm_mul, norm_mul, norm_exp_lam, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnpos]
  gcongr
  unfold Amp at hA
  exact hA

/-- The small quantity `δ_n` on the disc. -/
noncomputable def deltaN (a η n y₁ : ℝ) : ℝ := (cE a η + 1) / n + Real.exp (-(2 * π * n * y₁))

lemma cE_pos {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) : 0 < cE a η := by
  unfold cE
  have : 0 < Real.sin (η / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  positivity

/-- **(M)**: on the disc, `G_n(nx) e^{-λ_n - nΩ}/n ≈ e^{n(f(x) - Ω)} A(x)`. -/
theorem Gfn_disc_approx (m : ℕ) {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) {x : ℂ}
    (hxim : 0 < x.im) (hx : SectorAt a η x) {R y₁ : ℝ} (hR : ‖x‖ ≤ R)
    (hy₁ : y₁ ≤ x.im) (Ω : ℂ) (hn : LargeN a η (Z7.nOf m : ℝ))
    (hδ : deltaN a η (Z7.nOf m : ℝ) y₁ ≤ 1) :
    ‖Gfn m ((Z7.nOf m : ℝ) * x) * Complex.exp (-(lamN (Z7.nOf m) + (Z7.nOf m : ℝ) * Ω))
        / (Z7.nOf m : ℝ) - Complex.exp ((Z7.nOf m : ℝ) * (phaseZ x - Ω)) * Alim x‖
      ≤ ‖Complex.exp ((Z7.nOf m : ℝ) * (phaseZ x - Ω))‖ *
        (100 * Bgrowth a R ^ 2 * deltaN a η (Z7.nOf m : ℝ) y₁) := by
  obtain ⟨hn1, hn2, hn3⟩ := hn
  set n : ℝ := (Z7.nOf m : ℝ) with hn_def
  have hnpos : 0 < n := by linarith
  obtain ⟨e, he, hF⟩ := Gfn_path m ha hη0 hη hxim hx hn1
  rw [← hn_def] at hF he
  have hxsec : ∀ i, a ≤ ‖alphaZ i x‖ := fun i => (hx i).1
  obtain ⟨gX, gE⟩ := growth_bounds ha hxsec hR
  have hB : 1 ≤ Bgrowth a R := one_le_Bgrowth a ((norm_nonneg x).trans hR)
  set δ := deltaN a η n y₁ with hδdef
  have hcE := cE_pos ha hη0 hη
  have hδ0 : 0 ≤ δ := by rw [hδdef]; unfold deltaN; positivity
  have he' : ‖e‖ ≤ δ := by
    refine he.trans ?_
    rw [hδdef]; unfold deltaN
    have : cE a η / n ≤ (cE a η + 1) / n := by gcongr; linarith
    have := Real.exp_pos (-(2 * π * n * y₁))
    linarith
  have hq : ‖Complex.exp (2 * π * I * ((n : ℂ) * x))‖ ≤ δ := by
    rw [norm_exp_two_pi_I_mul, hδdef]; unfold deltaN
    have h1 : Real.exp (-(2 * π * n * x.im)) ≤ Real.exp (-(2 * π * n * y₁)) := by
      gcongr
    have : 0 ≤ (cE a η + 1) / n := by positivity
    linarith
  have hA := amp_diff_bound (x := x) (e := e) (q := Complex.exp (2 * π * I * ((n : ℂ) * x)))
    hB hδ0 hδ gX gE he' hq
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hrewrite : Gfn m ((n : ℂ) * x) * Complex.exp (-(lamN n + (n : ℂ) * Ω)) / n
      = Complex.exp ((n : ℂ) * (phaseZ x - Ω)) *
          Amp x e (Complex.exp (2 * π * I * ((n : ℂ) * x))) := by
    rw [hF]
    unfold Amp
    have hexp : Complex.exp (lamN n + (n : ℂ) * phaseZ x) * Complex.exp (-(lamN n + (n : ℂ) * Ω))
        = Complex.exp ((n : ℂ) * (phaseZ x - Ω)) := by
      rw [← Complex.exp_add]; congr 1; ring
    field_simp
    rw [← hexp]
    ring
  rw [hrewrite, ← mul_sub, norm_mul]
  gcongr

end ZetaIrr.Z7.Analytic
