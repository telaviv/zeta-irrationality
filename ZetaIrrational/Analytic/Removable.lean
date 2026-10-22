/-
# Finitely many removable singularities

`exists_removable`: if `G` is differentiable on a punctured ball around each point `t` of a finite
set `S`, and `(z - t) G(z) → 0` as `z → t`, then `G` can be redefined on `S` to be differentiable
at every point of `S` (and wherever `G` was already differentiable off `S`). This is Mathlib's
`Complex.differentiableOn_update_limUnder_of_isLittleO`, applied pointwise.

It replaces the residue theorem in `ContourCot.lean`: subtracting the principal parts
`f(t) m_{t,s}(z)` leaves a function with removable singularities only, to which Cauchy's theorem
for rectangles applies.
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace ZetaIrr.Analytic

open Complex Real Filter Topology Metric Set

/-- **Finitely many removable singularities.** -/
theorem exists_removable {G : ℂ → ℂ} (S : Finset ℂ)
    (hS : ∀ t ∈ S, ∃ r > 0, (∀ z ∈ ball t r, z ≠ t → z ∉ S ∧ DifferentiableAt ℂ G z) ∧
      Tendsto (fun z => (z - t) * G z) (𝓝[≠] t) (𝓝 0)) :
    ∃ G' : ℂ → ℂ, (∀ z ∉ S, G' z = G z) ∧ (∀ t ∈ S, DifferentiableAt ℂ G' t) ∧
      (∀ z, z ∉ S → DifferentiableAt ℂ G z → DifferentiableAt ℂ G' z) := by
  classical
  let G' : ℂ → ℂ := fun z => if z ∈ S then limUnder (𝓝[≠] z) G else G z
  refine ⟨G', fun z hz => by simp [G', hz], ?_, ?_⟩
  · intro t ht
    obtain ⟨r, hr, hball, hlim⟩ := hS t ht
    have hU : ball t r ∈ 𝓝 t := ball_mem_nhds t hr
    have hd : DifferentiableOn ℂ G (ball t r \ {t}) := fun z hz =>
      (hball z hz.1 hz.2).2.differentiableWithinAt
    have hsub : Tendsto (fun z : ℂ => z - t) (𝓝[≠] t) (𝓝 0) := by
      have h : Tendsto (fun z : ℂ => z - t) (𝓝 t) (𝓝 (t - t)) :=
        ((continuous_id (X := ℂ)).sub (continuous_const (y := t))).tendsto t
      rw [sub_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    have ho : (fun z => G z - G t) =o[𝓝[≠] t] fun z => (z - t)⁻¹ := by
      rw [Asymptotics.isLittleO_iff_tendsto']
      · have h2 : Tendsto (fun z => (z - t) * G t) (𝓝[≠] t) (𝓝 0) := by
          simpa using hsub.mul_const (G t)
        have h3 : Tendsto (fun z => (z - t) * G z - (z - t) * G t) (𝓝[≠] t) (𝓝 0) := by
          simpa using hlim.sub h2
        refine h3.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        have : z - t ≠ 0 := sub_ne_zero.2 hz
        field_simp
      · filter_upwards [self_mem_nhdsWithin] with z hz h0
        exact absurd h0 (inv_ne_zero (sub_ne_zero.2 hz))
    have hdu := Complex.differentiableOn_update_limUnder_of_isLittleO hU hd ho
    have heq : G' =ᶠ[𝓝 t] Function.update G t (limUnder (𝓝[≠] t) G) := by
      filter_upwards [hU] with z hz
      by_cases hzt : z = t
      · subst hzt; simp [G', ht]
      · simp [G', Function.update_of_ne hzt, (hball z hz hzt).1]
    exact (hdu.differentiableAt hU).congr_of_eventuallyEq heq
  · intro z hz hd
    have heq : G' =ᶠ[𝓝 z] G := by
      have : (↑S : Set ℂ)ᶜ ∈ 𝓝 z := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hz
      filter_upwards [this] with w hw
      have hw' : w ∉ S := by simpa using hw
      simp only [G', hw', ↓reduceIte]
    exact hd.congr_of_eventuallyEq heq

end ZetaIrr.Analytic
