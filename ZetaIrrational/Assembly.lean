/-
# Assembly: logarithmic bounds force `D_m L_m → 0`

If `log D_m + log |L_m| ≤ n_m (Q + ε_m)` whenever `L_m ≠ 0`, with `Q < 0`, `ε_m → 0`, `D_m > 0` and
`n_m ≥ m`, then `D_m · L_m → 0`. This is the analytic content of the contradiction step: the
`G log n!` terms of Lemmas 4 and 6 have already cancelled in the hypothesis.
-/
import Mathlib

namespace ZetaIrr

open Filter Topology

theorem tendsto_mul_zero_of_log_bound (D L : ℕ → ℝ) (n : ℕ → ℕ) (hn : ∀ m, m ≤ n m)
    (hD : ∀ m, 0 < D m) (Q : ℝ) (hQ : Q < 0) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hb : ∀ᶠ m in atTop, L m ≠ 0 → Real.log (D m) + Real.log |L m| ≤ (n m : ℝ) * (Q + ε m)) :
    Tendsto (fun m => D m * L m) atTop (𝓝 0) := by
  have hQ2 : Q / 2 < 0 := by linarith
  have hε' : ∀ᶠ m in atTop, ε m ≤ -Q / 2 := hε (Iic_mem_nhds (by linarith))
  -- eventually `|D m L m| ≤ exp(Q/2)^m`
  have hbound : ∀ᶠ m in atTop, ‖D m * L m‖ ≤ Real.exp (Q / 2) ^ m := by
    filter_upwards [hb, hε'] with m hbm hεm
    rw [Real.norm_eq_abs]
    by_cases hL : L m = 0
    · simp [hL, pow_nonneg (Real.exp_pos _).le]
    have hDL : D m * L m ≠ 0 := mul_ne_zero (hD m).ne' hL
    have hpos : 0 < |D m * L m| := abs_pos.mpr hDL
    rw [← Real.exp_nat_mul, ← Real.exp_log hpos, Real.exp_le_exp, abs_mul, abs_of_pos (hD m),
      Real.log_mul (hD m).ne' (abs_ne_zero.mpr hL)]
    have hnm : (m : ℝ) ≤ (n m : ℝ) := by exact_mod_cast hn m
    have hn0 : (0 : ℝ) ≤ (n m : ℝ) := Nat.cast_nonneg _
    calc Real.log (D m) + Real.log |L m| ≤ (n m : ℝ) * (Q + ε m) := hbm hL
      _ ≤ (n m : ℝ) * (Q / 2) := by
          apply mul_le_mul_of_nonneg_left _ hn0
          linarith
      _ ≤ (m : ℝ) * (Q / 2) := by nlinarith
  have hlim : Tendsto (fun m : ℕ => Real.exp (Q / 2) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le (by
      have h := Real.exp_lt_exp.mpr hQ2
      rwa [Real.exp_zero] at h)
  exact squeeze_zero_norm' hbound hlim

end ZetaIrr
