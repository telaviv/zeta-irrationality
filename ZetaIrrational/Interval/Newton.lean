/-
# Existence and uniqueness of a zero by a contraction (interval-Newton / Krawczyk type)

`exists_unique_zero_of_contraction`: let `g` be complex-differentiable on the closed disc
`closedBall c R` with derivative `g'`, let `Y ≠ 0`, and suppose
* `‖1 - Y g'(z)‖ ≤ κ < 1` on the disc,
* `‖Y g(c)‖ ≤ ε` and `ε + κ R ≤ R`.

Then `g` has exactly one zero in the disc. Proof: `T z = z - Y g z` maps the disc into itself and
is a `κ`-contraction there (mean value inequality on the convex disc); Banach's fixed point theorem
(`ContractingWith.exists_fixedPoint'`) gives the fixed point, and the contraction gives uniqueness.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Contracting

namespace ZetaIrr.Interval

open Metric Set

theorem exists_unique_zero_of_contraction {g g' : ℂ → ℂ} {c Y : ℂ} {R κ ε : ℝ}
    (hY : Y ≠ 0) (hR : 0 ≤ R)
    (hg : ∀ z ∈ closedBall c R, HasDerivAt g (g' z) z)
    (hκ : ∀ z ∈ closedBall c R, ‖1 - Y * g' z‖ ≤ κ) (hκ1 : κ < 1)
    (hε : ‖Y * g c‖ ≤ ε) (hεR : ε + κ * R ≤ R) :
    ∃! z, z ∈ closedBall c R ∧ g z = 0 := by
  set s := closedBall c R with hs
  have hc : c ∈ s := mem_closedBall_self hR
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ c hc)
  set T : ℂ → ℂ := fun z => z - Y * g z with hTdef
  have hT : ∀ z ∈ s, HasDerivWithinAt T (1 - Y * g' z) s z := fun z hz =>
    ((hasDerivAt_id z).sub ((hg z hz).const_mul Y)).hasDerivWithinAt
  have hlip : ∀ x ∈ s, ∀ y ∈ s, ‖T y - T x‖ ≤ κ * ‖y - x‖ := fun x hx y hy =>
    (convex_closedBall c R).norm_image_sub_le_of_norm_hasDerivWithin_le hT hκ hx hy
  have hmaps : MapsTo T s s := by
    intro z hz
    have hz' : ‖z - c‖ ≤ R := by rw [← dist_eq_norm]; exact hz
    have h1 := hlip c hc z hz
    have h2 : ‖T c - c‖ ≤ ε := by
      have : T c - c = -(Y * g c) := by simp [hTdef]
      rw [this, norm_neg]; exact hε
    rw [hs, mem_closedBall, dist_eq_norm]
    calc ‖T z - c‖ = ‖(T z - T c) + (T c - c)‖ := by ring_nf
      _ ≤ ‖T z - T c‖ + ‖T c - c‖ := norm_add_le _ _
      _ ≤ κ * ‖z - c‖ + ε := add_le_add h1 h2
      _ ≤ κ * R + ε := by gcongr
      _ ≤ R := by linarith
  have hfix : ∀ z, T z = z → g z = 0 := fun z h => by
    have : Y * g z = 0 := by
      have h' : z - Y * g z = z := h
      linear_combination -h'
    exact (mul_eq_zero.1 this).resolve_left hY
  have hzero : ∀ z, g z = 0 → T z = z := by intro z h; simp [hTdef, h]
  have hcontr : ContractingWith (Real.toNNReal κ) (hmaps.restrict T s s) := by
    refine ⟨Real.toNNReal_lt_one.2 hκ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm,
      Real.coe_toNNReal _ hκ0]
    exact hlip y y.2 x x.2
  obtain ⟨y, hys, hyfix, -, -⟩ :=
    ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hcontr hc
      (edist_ne_top _ _)
  refine ⟨y, ⟨hys, hfix y hyfix⟩, fun w ⟨hws, hw⟩ => ?_⟩
  have h := hlip y hys w hws
  rw [hzero w hw, hzero y (hfix y hyfix)] at h
  have : ‖w - y‖ = 0 := by
    have hn := norm_nonneg (w - y)
    nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end ZetaIrr.Interval
