/-
# The Z7 factor list and phase, list form (instance Z7)

Instance Z7: `r = 11/12`, `q = 240`, zero multiplicity 5; factor list (`c, s, κ` with `α = s x + κ`)

    (5, x), (5, 11/12 - x), (5, x + 23/12), (-5, x + 1), and for each block k = 1..18, δ = k/80:
    (1, x + δ), (-1, x + 1 - δ),

40 factors, in the order of the analytic factor list `Z7/Analytic/Factors.lean`.

Definitions (principal `Complex.log`): `Ψ = psiL facZ7`, `f z = Ψ z - 3πi z`, `g z = Ψ'(z) - 3πi`,
with the derivative chain `f → g → Ψ'' → Ψ'''` on `Im z ≠ 0`.

This file has no expensive kernel checks; every other file of the Z7 certificate imports it.
-/
import ZetaIrrational.Interval.Psi
import ZetaIrrational.Interval.Segment
import ZetaIrrational.FamilyZ7

namespace ZetaIrr.Z7.Interval

open Complex ZetaIrr.Interval Real

/-- Factor list of instance Z7 (`c, s, κ` with `α = s x + κ`). -/
def facZ7 : List Fac :=
  [⟨5, 1, 0⟩, ⟨5, -1, 11 / 12⟩, ⟨5, 1, 23 / 12⟩, ⟨-5, 1, 1⟩,
   ⟨1, 1, 1 / 80⟩, ⟨-1, 1, 79 / 80⟩, ⟨1, 1, 2 / 80⟩, ⟨-1, 1, 78 / 80⟩,
   ⟨1, 1, 3 / 80⟩, ⟨-1, 1, 77 / 80⟩, ⟨1, 1, 4 / 80⟩, ⟨-1, 1, 76 / 80⟩,
   ⟨1, 1, 5 / 80⟩, ⟨-1, 1, 75 / 80⟩, ⟨1, 1, 6 / 80⟩, ⟨-1, 1, 74 / 80⟩,
   ⟨1, 1, 7 / 80⟩, ⟨-1, 1, 73 / 80⟩, ⟨1, 1, 8 / 80⟩, ⟨-1, 1, 72 / 80⟩,
   ⟨1, 1, 9 / 80⟩, ⟨-1, 1, 71 / 80⟩, ⟨1, 1, 10 / 80⟩, ⟨-1, 1, 70 / 80⟩,
   ⟨1, 1, 11 / 80⟩, ⟨-1, 1, 69 / 80⟩, ⟨1, 1, 12 / 80⟩, ⟨-1, 1, 68 / 80⟩,
   ⟨1, 1, 13 / 80⟩, ⟨-1, 1, 67 / 80⟩, ⟨1, 1, 14 / 80⟩, ⟨-1, 1, 66 / 80⟩,
   ⟨1, 1, 15 / 80⟩, ⟨-1, 1, 65 / 80⟩, ⟨1, 1, 16 / 80⟩, ⟨-1, 1, 64 / 80⟩,
   ⟨1, 1, 17 / 80⟩, ⟨-1, 1, 63 / 80⟩, ⟨1, 1, 18 / 80⟩, ⟨-1, 1, 62 / 80⟩]

lemma facZ7_s : ∀ a ∈ facZ7, a.s ≠ 0 := by decide

lemma facZ7_s1 : ∀ a ∈ facZ7, a.s = 1 ∨ a.s = -1 := by decide

/-! ## Analytic objects -/

/-- `Ψ(z) = Σ c_i α_i(z) log α_i(z)`. -/
noncomputable def Ψ : ℂ → ℂ := psiL facZ7

/-- `f(z) = Ψ(z) - 3πi z` (definitionally the list form `fL 3 facZ7`). -/
noncomputable def f : ℂ → ℂ := fL 3 facZ7

/-- `g(z) = Ψ'(z) - 3πi` (definitionally `gL 3 facZ7`). -/
noncomputable def g : ℂ → ℂ := gL 3 facZ7

lemma f_eq_fL : f = fL 3 facZ7 := rfl

lemma g_eq_gL : g = gL 3 facZ7 := rfl

lemma f_apply (z : ℂ) : f z = Ψ z - 3 * π * I * z := by
  simp only [f, fL, Ψ]; push_cast; ring

lemma g_apply (z : ℂ) : g z = dpsiL facZ7 z - 3 * π * I := by
  simp only [g, gL]; push_cast; ring

lemma good_of_im {z : ℂ} (hz : z.im ≠ 0) : Good facZ7 z := good_of_im_ne_zero facZ7_s hz

lemma Z7_hasDerivAt_f {z : ℂ} (hz : z.im ≠ 0) : HasDerivAt f (g z) z := by
  rw [f_eq_fL, g_eq_gL]; exact hasDerivAt_fL (good_of_im hz)

lemma Z7_hasDerivAt_g {z : ℂ} (hz : z.im ≠ 0) : HasDerivAt g (d2psiL facZ7 z) z := by
  rw [g_eq_gL]; exact hasDerivAt_gL (good_of_im hz)

end ZetaIrr.Z7.Interval
