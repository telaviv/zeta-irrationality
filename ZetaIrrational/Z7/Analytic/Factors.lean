/-
# The Z7 factor list and the phase (Lemma 6; `r = 11/12`, 18 blocks)

Forty Γ-factors `(c_i, s_i, u_i, β_i)`, `α_i(x) = s_i x + u_i`, so that for `z` not an integer

    R_n(z) = (2z + n) · Π_i Γ(s_i z + n u_i + β_i)^{c_i} · sin⁵(πz)/π⁵

(`Gamma.lean`):
* `i = 0`: `(5, +1, 0, 0)` (`Γ(z)⁵`); `i = 1`: `(5, -1, 11/12, 1)` (`Γ(rn + 1 - z)⁵`);
* `i = 2`: `(5, +1, 23/12, 1)` (`Γ(z + (1+r)n + 1)⁵`); `i = 3`: `(-5, +1, 1, 1)` (`Γ(z + n + 1)⁻⁵`);
* block `j = 0..17` with `k = j + 1` (`δ = k/80`):
  `i = 4 + 2j`: `(1, +1, k/80, 0)`, `i = 5 + 2j`: `(-1, +1, 1 - k/80, 1)`.

Identities: `Σ c_i s_i = 0`, `Σ c_i u_i = -G = -547/120`, `Σ c_i (β_i - 1/2) = -18 = -S`,
`Σ c_i = 10`, `Σ |c_i| = 56`, `Σ |c_i (β_i - 1/2)| = 28`.

Phase functions: `alphaZ`, `PsiZ = Σ c_i α_i log α_i`, `Psi1Z = Σ c_i s_i log α_i`,
`Psi2Z = Σ c_i s_i²/α_i`, `Psi3Z = -Σ c_i s_i³/α_i²`, `psi0Z = Σ c_i (β_i - 1/2) log α_i`,
`phaseZ = PsiZ - 3πi x` (the integrand carries `e^{-3πiz}`, `T_eq_exp` in `CotKernel.lean`),
`lamN`, `SectorAt`.

It imports only Mathlib.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace ZetaIrr.Z7.Analytic

open Complex Real Finset

/-- `c_i`. -/
def cZ : Fin 40 → ℤ :=
  ![5, 5, 5, -5, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1]

/-- `s_i`. -/
def sZ : Fin 40 → ℝ :=
  ![1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- `u_i`. -/
noncomputable def uZ : Fin 40 → ℝ :=
  ![0, 11 / 12, 23 / 12, 1, 1 / 80, 79 / 80, 2 / 80, 78 / 80, 3 / 80, 77 / 80, 4 / 80, 76 / 80,
    5 / 80, 75 / 80, 6 / 80, 74 / 80, 7 / 80, 73 / 80, 8 / 80, 72 / 80, 9 / 80, 71 / 80,
    10 / 80, 70 / 80, 11 / 80, 69 / 80, 12 / 80, 68 / 80, 13 / 80, 67 / 80, 14 / 80, 66 / 80,
    15 / 80, 65 / 80, 16 / 80, 64 / 80, 17 / 80, 63 / 80, 18 / 80, 62 / 80]

/-- `β_i`. -/
noncomputable def βZ : Fin 40 → ℝ :=
  ![0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

lemma sum_cs : ∑ i, (cZ i : ℝ) * sZ i = 0 := by
  norm_num [Fin.sum_univ_succ, cZ, sZ]

lemma sum_cu : ∑ i, (cZ i : ℝ) * uZ i = -(547 / 120) := by
  norm_num [Fin.sum_univ_succ, cZ, uZ]

lemma sum_cβ : ∑ i, (cZ i : ℝ) * (βZ i - 1 / 2) = -18 := by
  norm_num [Fin.sum_univ_succ, cZ, βZ]

lemma sum_c : ∑ i, (cZ i : ℝ) = 10 := by
  norm_num [Fin.sum_univ_succ, cZ]

lemma sum_abs_c : ∑ i, |(cZ i : ℝ)| = 56 := by
  norm_num [Fin.sum_univ_succ, cZ]

lemma sum_abs_cβ : ∑ i, |(cZ i : ℝ) * (βZ i - 1 / 2)| = 28 := by
  norm_num [Fin.sum_univ_succ, cZ, βZ]

lemma sZ_sq (i : Fin 40) : sZ i ^ 2 = 1 := by
  fin_cases i <;> simp [sZ]

lemma βZ_bounds (i : Fin 40) : 0 ≤ βZ i ∧ βZ i ≤ 2 := by
  fin_cases i <;> simp [βZ]

lemma uZ_bound (i : Fin 40) : |uZ i| ≤ 2 := by
  fin_cases i <;> simp [uZ] <;> norm_num [abs_of_nonneg]

/-- `α_i(x) = s_i x + u_i`. -/
noncomputable def alphaZ (i : Fin 40) (x : ℂ) : ℂ := sZ i * x + uZ i

/-- `Ψ(x) = Σ c_i α_i log α_i`. -/
noncomputable def PsiZ (x : ℂ) : ℂ := ∑ i, (cZ i : ℂ) * (alphaZ i x * Complex.log (alphaZ i x))

/-- `Ψ'(x) = Σ c_i s_i log α_i`. -/
noncomputable def Psi1Z (x : ℂ) : ℂ := ∑ i, (cZ i : ℂ) * sZ i * Complex.log (alphaZ i x)

/-- `Ψ''(x) = Σ c_i s_i² / α_i`. -/
noncomputable def Psi2Z (x : ℂ) : ℂ := ∑ i, (cZ i : ℂ) * sZ i ^ 2 / alphaZ i x

/-- `Ψ'''(x) = -Σ c_i s_i³ / α_i²`. -/
noncomputable def Psi3Z (x : ℂ) : ℂ := -∑ i, (cZ i : ℂ) * sZ i ^ 3 / alphaZ i x ^ 2

/-- `ψ₀(x) = Σ c_i (β_i - 1/2) log α_i`. -/
noncomputable def psi0Z (x : ℂ) : ℂ := ∑ i, (cZ i : ℂ) * (βZ i - 1 / 2) * Complex.log (alphaZ i x)

/-- The phase `f(x) = Ψ(x) - 3πi x`. -/
noncomputable def phaseZ (x : ℂ) : ℂ := PsiZ x - 3 * π * I * x

/-- `λ_n = -G n log n + G n - 18 log n + 5 log 2π` (`G = 547/120`). -/
noncomputable def lamN (n : ℝ) : ℝ :=
  -(547 / 120) * n * Real.log n + (547 / 120) * n - 18 * Real.log n + 5 * Real.log (2 * π)

/-- The sector condition (S4) at `x`. -/
def SectorAt (a η : ℝ) (x : ℂ) : Prop :=
  ∀ i, a ≤ ‖alphaZ i x‖ ∧ |Complex.arg (alphaZ i x)| ≤ π - η

end ZetaIrr.Z7.Analytic
