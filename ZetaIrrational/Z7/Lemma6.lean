/-
# Lemma 6 for Z7, unconditional

`size_of_saddleData` and `nonvan_of_saddleData` (`Z7/Analytic/NonvanZ7.lean`, PROOF_ZETA §6) applied to the
kernel-checked saddle certificate `Z7_saddleData` (`Z7/Interval/SaddleDataZ7.lean`):
* `size_Z7`: `log |L_n| ≤ -G log n! + n (Vcert + o(1))` with `Vcert = -10.1167` (Lemma 6(i));
* `nonvan_Z7`: `L_n ≠ 0` for infinitely many `n` (Lemma 6(ii)).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Analytic.NonvanZ7
import ZetaIrrational.Z7.Interval.SaddleDataZ7

namespace ZetaIrr.Z7

open Filter Topology

/-- **Lemma 6(i) for Z7.** -/
theorem size_Z7 : ∃ εL : ℕ → ℝ, Tendsto εL atTop (𝓝 0) ∧ ∀ᶠ m in atTop, L m ≠ 0 →
    Real.log |L m| ≤ -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * ((Vcert : ℝ) + εL m) :=
  Analytic.size_of_saddleData Interval.Z7_saddleData

/-- **Lemma 6(ii) for Z7.** -/
theorem nonvan_Z7 : ∃ᶠ m in atTop, L m ≠ 0 :=
  Analytic.nonvan_of_saddleData Interval.Z7_saddleData

end ZetaIrr.Z7
