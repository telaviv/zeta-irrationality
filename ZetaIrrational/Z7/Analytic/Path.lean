/-
# The integrand on the contour: `G_n(nx) = e^{λ_n + n f(x)} · n · A_n(x)` (PROOF_ZETA §6.5)

`G_n = R_n k₄` (`ContourZ7.lean`). Off the real axis,
`G_n(z) = P_n(z) T(z)` with `T(z) = 8 cos(πz)(cos²(πz) + 2) = e^{-3πiz}(1 + 11q + 11q² + q³)`,
`q = e^{2πiz}` (`Gfn_eq_PT`, from `sin⁵(πz) k₄(z) = π⁵ T(z)` and the Γ-form of `R_n`). With
Stirling (`Pfun_asymp`), for `Im x > 0`, the sector condition at `x`, and `n ≥ 4/a`:

    G_n(nx) = e^{λ_n + n f(x)} · n · A_n(x),   A_n(x) = (2x + 1) e^{ψ₀(x) + e} Q(q),     (`Gfn_path`)

`f = Ψ - 3πix`, `Q(q) = 1 + 11q + 11q² + q³`, `|e| ≤ c_e/n`. The abstract bounds
* `amp_bound` (for (U)): `|A_n(x)| ≤ 72 B²` (`|q| ≤ 1`, `|e| ≤ 1`);
* `amp_diff_bound` (for (M)): `|A_n(x) - A(x)| ≤ 100 B² δ`, `A(x) = (2x + 1) e^{ψ₀(x)}`,
for any `B ≥ 1` dominating `|2x+1|`, `|e^{ψ₀(x)}|`, and `δ ≤ 1` dominating `|e|`, `|q|`.
`growth_bounds` gives such a `B` from `‖x‖` alone.

Compared with lean_beta's `FnPath.lean` there are no logarithmic derivatives `μ, μ'`: the four
derivatives of `R_n⁗` were moved onto the kernel (`ContourZ7.lean`).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Analytic.PathAsymp
import ZetaIrrational.Z7.Analytic.ContourZ7

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Real Finset Filter Topology
open ZetaIrr.Analytic ZetaIrr.Fam.Analytic

/-- `G_n = P_n T` off the real axis. -/
theorem Gfn_eq_PT (m : ℕ) {z : ℂ} (hz : z.im ≠ 0) : Gfn m z = Pfun m z * Tfun z := by
  have hs := sin_pi_ne_zero_of_im hz
  have hk := sin_pow_five_mul_kk4 hs
  have hπ := hπC'
  unfold Gfn
  rw [RC_eq_Pfun m z hz]
  calc Pfun m z * Complex.sin (π * z) ^ 5 / (π : ℂ) ^ 5 * kk 4 z
      = Pfun m z * (Complex.sin (π * z) ^ 5 * kk 4 z) / (π : ℂ) ^ 5 := by ring
    _ = Pfun m z * Tfun z := by rw [hk]; field_simp

/-- `Q(q) = 1 + 11q + 11q² + q³`. -/
noncomputable def Qz (q : ℂ) : ℂ := 1 + 11 * q + 11 * q ^ 2 + q ^ 3

/-- The Stirling error constant. -/
noncomputable def cE (a η : ℝ) : ℝ := 56 * ((9 + 1 / (6 * Real.sin (η / 2) ^ 2)) / a)

/-- **The integrand on the contour.** -/
theorem Gfn_path (m : ℕ) {a η : ℝ} (ha : 0 < a) (hη0 : 0 < η) (hη : η ≤ π) {x : ℂ}
    (hxim : 0 < x.im) (hx : SectorAt a η x) (hn : 4 / a ≤ (Z7.nOf m : ℝ)) :
    ∃ e : ℂ, ‖e‖ ≤ cE a η / (Z7.nOf m : ℝ) ∧
      Gfn m ((Z7.nOf m : ℝ) * x) =
        Complex.exp (lamN (Z7.nOf m) + (Z7.nOf m : ℝ) * phaseZ x) * ((Z7.nOf m : ℝ) : ℂ) *
          ((2 * x + 1) * Complex.exp (psi0Z x + e) *
            Qz (Complex.exp (2 * π * I * ((Z7.nOf m : ℝ) * x)))) := by
  set n : ℝ := (Z7.nOf m : ℝ) with hn_def
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  obtain ⟨e, he, hP⟩ := Pfun_asymp m ha hη0 hη hx hn
  refine ⟨e, ?_, ?_⟩
  · refine he.trans (le_of_eq ?_)
    unfold cE; rw [← hn_def]; field_simp
  have hzim : ((n : ℂ) * x).im ≠ 0 := by
    have : ((n : ℂ) * x).im = n * x.im := by simp
    rw [this]; exact (mul_pos hnpos hxim).ne'
  rw [Gfn_eq_PT m hzim, hP, T_eq_exp]
  have hexp : Complex.exp (lamN n + n * PsiZ x + psi0Z x + e) *
      Complex.exp (-(3 * π * I * ((n : ℂ) * x)))
      = Complex.exp (lamN n + n * phaseZ x) * Complex.exp (psi0Z x + e) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold phaseZ; ring
  unfold Qz
  calc (n : ℂ) * (2 * x + 1) * Complex.exp (lamN n + n * PsiZ x + psi0Z x + e) *
        (Complex.exp (-(3 * π * I * ((n : ℂ) * x))) *
          (1 + 11 * Complex.exp (2 * π * I * ((n : ℂ) * x))
            + 11 * Complex.exp (2 * π * I * ((n : ℂ) * x)) ^ 2
            + Complex.exp (2 * π * I * ((n : ℂ) * x)) ^ 3))
      = (Complex.exp (lamN n + n * PsiZ x + psi0Z x + e) *
          Complex.exp (-(3 * π * I * ((n : ℂ) * x)))) * (n : ℂ) * ((2 * x + 1) *
          (1 + 11 * Complex.exp (2 * π * I * ((n : ℂ) * x))
            + 11 * Complex.exp (2 * π * I * ((n : ℂ) * x)) ^ 2
            + Complex.exp (2 * π * I * ((n : ℂ) * x)) ^ 3)) := by ring
    _ = _ := by rw [hexp]; ring

/-! ### Abstract amplitude bounds -/

/-- The amplitude `A_n` as a function of the data. -/
noncomputable def Amp (x e q : ℂ) : ℂ := (2 * x + 1) * Complex.exp (psi0Z x + e) * Qz q

/-- The limiting amplitude `A(x) = (2x+1) e^{ψ₀(x)}`. -/
noncomputable def Alim (x : ℂ) : ℂ := (2 * x + 1) * Complex.exp (psi0Z x)

/-- **(U)-type bound** for the amplitude. -/
theorem amp_bound {x e q : ℂ} {B : ℝ} (hB : 1 ≤ B) (hX : ‖2 * x + 1‖ ≤ B)
    (hE : ‖Complex.exp (psi0Z x)‖ ≤ B) (hq : ‖q‖ ≤ 1) (he : ‖e‖ ≤ 1) :
    ‖Amp x e q‖ ≤ 72 * B ^ 2 := by
  unfold Amp Qz
  rw [norm_mul, norm_mul, Complex.exp_add, norm_mul]
  have h2 := norm_exp_le_three he
  have h3 := norm_Qz_le hq
  calc ‖2 * x + 1‖ * (‖Complex.exp (psi0Z x)‖ * ‖Complex.exp e‖) *
        ‖1 + 11 * q + 11 * q ^ 2 + q ^ 3‖ ≤ B * (B * 3) * 24 := by gcongr
    _ = 72 * B ^ 2 := by ring

/-- **(M)-type bound**: `|A_n - A| ≤ 100 B² δ`. -/
theorem amp_diff_bound {x e q : ℂ} {B δ : ℝ} (hB : 1 ≤ B) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hX : ‖2 * x + 1‖ ≤ B) (hE : ‖Complex.exp (psi0Z x)‖ ≤ B) (he : ‖e‖ ≤ δ) (hq : ‖q‖ ≤ δ) :
    ‖Amp x e q - Alim x‖ ≤ 100 * B ^ 2 * δ := by
  have he1 : ‖e‖ ≤ 1 := he.trans hδ
  have hq1 : ‖q‖ ≤ 1 := hq.trans hδ
  have hexp1 : ‖Complex.exp e - 1‖ ≤ 3 * δ := by
    calc ‖Complex.exp e - 1‖ ≤ ‖e‖ * Real.exp ‖e‖ := norm_cexp_sub_one_le_mul_exp e
      _ ≤ δ * 3 := by
          gcongr
          calc Real.exp ‖e‖ ≤ Real.exp 1 := Real.exp_le_exp.2 he1
            _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
      _ = 3 * δ := by ring
  have hQ := norm_Qz_le hq1
  have hQ1 := norm_Qz_sub_one_le hq1
  have hsplit : Amp x e q - Alim x = (2 * x + 1) * Complex.exp (psi0Z x) *
      ((Complex.exp e - 1) * Qz q + (Qz q - 1)) := by
    unfold Amp Alim
    rw [Complex.exp_add]
    ring
  rw [hsplit, norm_mul, norm_mul]
  have hinner : ‖(Complex.exp e - 1) * Qz q + (Qz q - 1)‖ ≤ 95 * δ := by
    unfold Qz
    calc _ ≤ ‖Complex.exp e - 1‖ * ‖1 + 11 * q + 11 * q ^ 2 + q ^ 3‖
          + ‖1 + 11 * q + 11 * q ^ 2 + q ^ 3 - 1‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ 3 * δ * 24 + 23 * δ :=
          add_le_add (mul_le_mul hexp1 hQ (norm_nonneg _) (by positivity))
            (hQ1.trans (by gcongr))
      _ = 95 * δ := by ring
  calc ‖2 * x + 1‖ * ‖Complex.exp (psi0Z x)‖ * ‖(Complex.exp e - 1) * Qz q + (Qz q - 1)‖
      ≤ B * B * (95 * δ) := by gcongr
    _ ≤ 100 * B ^ 2 * δ := by nlinarith [sq_nonneg B]

/-! ### Growth of `ψ₀` -/

lemma norm_alphaZ_le (i : Fin 40) (x : ℂ) : ‖alphaZ i x‖ ≤ ‖x‖ + 2 := by
  unfold alphaZ
  have hs : ‖(sZ i : ℂ)‖ = 1 := by
    have := sZ_sq i
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg (sZ i), sq_abs (sZ i)]
  have hu : ‖(uZ i : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact uZ_bound i
  calc ‖(sZ i : ℂ) * x + uZ i‖ ≤ ‖(sZ i : ℂ) * x‖ + ‖(uZ i : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖x‖ + 2 := by rw [norm_mul, hs, one_mul]; linarith

/-- `ℓ(r) = r + 2 + |log a| + π`. -/
noncomputable def ellA (a : ℝ) (r : ℝ) : ℝ := r + 2 + |Real.log a| + π

lemma norm_log_alphaZ_le {a : ℝ} (ha : 0 < a) {x : ℂ} (i : Fin 40) (hx : a ≤ ‖alphaZ i x‖) :
    ‖Complex.log (alphaZ i x)‖ ≤ ellA a ‖x‖ := by
  unfold ellA
  have := norm_log_le_of_ge ha hx
  have := norm_alphaZ_le i x
  linarith

lemma norm_cβ_eq (i : Fin 40) :
    ‖(cZ i : ℂ) * ((βZ i : ℂ) - 1 / 2)‖ = |(cZ i : ℝ) * (βZ i - 1 / 2)| := by
  rw [show ((cZ i : ℤ) : ℂ) * ((βZ i : ℂ) - 1 / 2)
      = ((((cZ i : ℤ) : ℝ) * (βZ i - 1 / 2) : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]

lemma norm_psi0Z_le {a : ℝ} (ha : 0 < a) {x : ℂ} (hx : ∀ i, a ≤ ‖alphaZ i x‖) :
    ‖psi0Z x‖ ≤ 28 * ellA a ‖x‖ := by
  unfold psi0Z
  refine (norm_sum_le _ _).trans ?_
  rw [← sum_abs_cβ, sum_mul]
  refine sum_le_sum (fun i _ => ?_)
  rw [norm_mul, norm_cβ_eq]
  exact mul_le_mul_of_nonneg_left (norm_log_alphaZ_le ha i (hx i)) (abs_nonneg _)

/-- A single bound `B(r) ≥ 1` dominating `‖2x+1‖` and `‖e^{ψ₀(x)}‖` for `‖x‖ ≤ r`. -/
noncomputable def Bgrowth (a r : ℝ) : ℝ := Real.exp (28 * ellA a r) + 2 * r + 1

lemma ellA_pos (a : ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 < ellA a r := by
  unfold ellA; have := Real.pi_pos; positivity

lemma one_le_Bgrowth (a : ℝ) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ Bgrowth a r := by
  unfold Bgrowth
  have := Real.exp_pos (28 * ellA a r)
  linarith

lemma Bgrowth_mono (a : ℝ) {r s : ℝ} (hrs : r ≤ s) : Bgrowth a r ≤ Bgrowth a s := by
  unfold Bgrowth ellA
  gcongr

theorem growth_bounds {a : ℝ} (ha : 0 < a) {x : ℂ} (hx : ∀ i, a ≤ ‖alphaZ i x‖) {r : ℝ}
    (hr : ‖x‖ ≤ r) :
    ‖2 * x + 1‖ ≤ Bgrowth a r ∧ ‖Complex.exp (psi0Z x)‖ ≤ Bgrowth a r := by
  have hmono := Bgrowth_mono a hr
  have hex := Real.exp_pos (28 * ellA a ‖x‖)
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hmono
    calc ‖2 * x + 1‖ ≤ ‖2 * x‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 * ‖x‖ + 1 := by simp
      _ ≤ Bgrowth a ‖x‖ := by unfold Bgrowth; linarith
  · refine le_trans ?_ hmono
    rw [Complex.norm_exp]
    calc Real.exp (psi0Z x).re ≤ Real.exp (28 * ellA a ‖x‖) := by
          gcongr
          exact (Complex.re_le_norm _).trans (norm_psi0Z_le ha hx)
      _ ≤ Bgrowth a ‖x‖ := by unfold Bgrowth; linarith [norm_nonneg x]

end ZetaIrr.Z7.Analytic
